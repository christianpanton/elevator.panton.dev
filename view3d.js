// view3d.js — Three.js first-person 3D view
// Depends on: app.js globals (latLonToUTM32, inDenmark, DHM_TOKEN, DHM_WCS, GeoTIFF)
// Exposes: window.View3D = { update, resize, setSatellite }

import * as THREE from 'https://cdn.jsdelivr.net/npm/three@0.165.0/+esm';

(function () {
  'use strict';

  // ── Themes ───────────────────────────────────────────────────────────────────
  const THEMES = {
    night: {
      sky:       0x0a1628,
      ground:    0x0d1a0d,
      terrain:   0x1a3a1a,
      terrainWf: 0x2a5a2a,
      hemiSky:   0x8ab4d0,
      hemiGnd:   0x1a2a10,
      hemiInt:   0.7,
      sunColor:  0xfff0dd,
      sunInt:    0.55,
      sunPos:    [1, 0.5, -0.8],
    },
    day: {
      sky:       0x7ec8e3,
      ground:    0x2d7a2d,
      terrain:   0x4a8c2a,
      terrainWf: 0x6ab03a,
      hemiSky:   0xd4e8ff,
      hemiGnd:   0x4a8020,
      hemiInt:   1.1,
      sunColor:  0xfffcf0,
      sunInt:    1.4,
      sunPos:    [0.3, 1.5, -0.5],
    },
  };

  const SUN_SVG  = `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.93 4.93l1.41 1.41M17.66 17.66l1.41 1.41M2 12h2M20 12h2M6.34 17.66l-1.41 1.41M19.07 4.93l-1.41 1.41"/></svg>`;
  const MOON_SVG = `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3a6 6 0 0 0 9 9 9 9 0 1 1-9-9Z"/></svg>`;

  // ── Constants ────────────────────────────────────────────────────────────────
  const GRID_RADIUS    = 2500;  // terrain tile half-width (m)
  const CACHE_SNAP     = 200;   // snap UTM to nearest N m for terrain cache key
  const SAT_SIZE       = 2048;  // satellite texture pixels
  const SAT_RADIUS     = 1000;  // satellite coverage half-width (m) — 2 km diameter
  const SAT_SNAP       = 0.005; // snap observer lat/lng (~0.5 km) for sat cache key
  const INNER_RADIUS   = 500;   // inner hi-res terrain patch half-width (m)
  const INNER_RES      = 256;   // inner patch grid resolution (256×256 → ~4 m/px)
  const INNER_SNAP     = 50;    // cache snap for inner patch (m)

  // ── Module state ─────────────────────────────────────────────────────────────
  let renderer, scene, camera, animId;
  let initialized    = false;
  let userHasDragged = false;
  let isDayMode      = false;
  let isSatelliteMode = false;

  let lastGrid      = null, lastGridKey      = null, pendingGridFetch  = false;
  let lastInnerGrid = null, lastInnerKey     = null, pendingInnerFetch = false;
  let satTex        = null, satTexKey        = null, pendingSatFetch   = false;
  let lastResults = null, lastObserver = null, lastObsElev = 0, lastR = 0;

  let yaw = 0, pitch = 0;
  let isPointerDown = false, lastPX = 0, lastPY = 0;

  // ── Init ─────────────────────────────────────────────────────────────────────
  function init() {
    const canvas = document.getElementById('view3d-canvas');
    renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));

    scene  = new THREE.Scene();
    camera = new THREE.PerspectiveCamera(60, 1, 0.5, 3e6);

    bindPointerEvents(canvas);

    document.getElementById('v3d-daynight').addEventListener('click', () => {
      isDayMode = !isDayMode;
      const btn = document.getElementById('v3d-daynight');
      btn.innerHTML = isDayMode ? MOON_SVG : SUN_SVG;
      btn.title     = isDayMode ? 'Switch to night' : 'Switch to day';
      rebuildScene();
    });

    initialized = true;
  }

  function rebuildScene() {
    if (!initialized) return;
    buildScene(lastResults, lastObserver, lastObsElev, lastR, lastGrid, lastInnerGrid);
  }

  // ── Coordinate helper ────────────────────────────────────────────────────────
  function toWorld(distM, bearingDeg, elevM) {
    const β = bearingDeg * Math.PI / 180;
    return new THREE.Vector3(distM * Math.sin(β), elevM, -distM * Math.cos(β));
  }

  // ── Terrain grid resolution from DOM ─────────────────────────────────────────
  function terrainGridRes() {
    const v = parseInt(document.getElementById('terrain-res').value);
    if (v === 0)  return 0;    // off
    if (v <= 256) return 128;  // low  → 128×128
    return 256;                // high → 256×256
  }

  // ── Satellite texture: Esri background + Kortforsyningen hi-res centre patch ──
  async function fetchSatelliteTexture(lat, lng) {
    const snapLat = Math.round(lat / SAT_SNAP) * SAT_SNAP;
    const snapLng = Math.round(lng / SAT_SNAP) * SAT_SNAP;
    const key = `${snapLat},${snapLng}`;
    if (key === satTexKey) return satTex;

    const Z       = 17;
    const TILE_PX = 256;
    const n       = Math.pow(2, Z);

    function worldX(lon) { return (lon + 180) / 360 * n * TILE_PX; }
    function worldY(la)  {
      const r = la * Math.PI / 180;
      return (1 - Math.log(Math.tan(r) + 1 / Math.cos(r)) / Math.PI) / 2 * n * TILE_PX;
    }

    const dLat = SAT_RADIUS / 111000;
    const dLon = SAT_RADIUS / (111000 * Math.cos(lat * Math.PI / 180));

    const wx1 = worldX(lng - dLon), wx2 = worldX(lng + dLon);
    const wy1 = worldY(lat + dLat), wy2 = worldY(lat - dLat); // north = smaller Y

    const txMin = Math.floor(wx1 / TILE_PX), txMax = Math.floor(wx2 / TILE_PX);
    const tyMin = Math.floor(wy1 / TILE_PX), tyMax = Math.floor(wy2 / TILE_PX);
    const numX  = txMax - txMin + 1;
    const numY  = tyMax - tyMin + 1;

    const tileCanvas = document.createElement('canvas');
    tileCanvas.width  = numX * TILE_PX;
    tileCanvas.height = numY * TILE_PX;
    const ctx = tileCanvas.getContext('2d');

    await Promise.all(Array.from({ length: numX * numY }, (_, k) => {
      const i = k % numX, j = Math.floor(k / numX);
      const url = `https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/${Z}/${tyMin + j}/${txMin + i}`;
      return fetch(url).then(r => r.blob()).then(blob => {
        const blobUrl = URL.createObjectURL(blob);
        return new Promise(resolve => {
          const img = new Image();
          img.onload  = () => { ctx.drawImage(img, i * TILE_PX, j * TILE_PX); URL.revokeObjectURL(blobUrl); resolve(); };
          img.onerror = () => { URL.revokeObjectURL(blobUrl); resolve(); };
          img.src = blobUrl;
        });
      }).catch(() => {});
    }));

    // Crop tile grid to exact geographic bbox, scale to SAT_SIZE
    const out = document.createElement('canvas');
    out.width = out.height = SAT_SIZE;
    out.getContext('2d').drawImage(
      tileCanvas,
      wx1 - txMin * TILE_PX, wy1 - tyMin * TILE_PX, wx2 - wx1, wy2 - wy1,
      0, 0, SAT_SIZE, SAT_SIZE
    );

    const tex = new THREE.CanvasTexture(out);
    if (renderer) tex.anisotropy = Math.min(renderer.capabilities.getMaxAnisotropy(), 16);
    satTex = tex; satTexKey = key;
    return tex;
  }

  function setSatLoadingUI(on) {
    document.getElementById('sat-spinner')?.classList.toggle('active', on);
    document.getElementById('view3d-sat-pulse')?.classList.toggle('active', on);
  }

  function triggerSatFetch(observer) {
    const snapLat = Math.round(observer.lat / SAT_SNAP) * SAT_SNAP;
    const snapLng = Math.round(observer.lng / SAT_SNAP) * SAT_SNAP;
    const key = `${snapLat},${snapLng}`;
    if (key === satTexKey || pendingSatFetch) return;
    pendingSatFetch = true;
    setSatLoadingUI(true);
    fetchSatelliteTexture(observer.lat, observer.lng).then(() => {
      pendingSatFetch = false;
      setSatLoadingUI(false);
      rebuildScene();
    });
  }

  // ── Terrain grid fetch ───────────────────────────────────────────────────────
  async function fetchTerrainGrid(lat, lng) {
    const gridRes = terrainGridRes();
    if (gridRes === 0 || !inDenmark(lat, lng)) return null;

    const obs   = latLonToUTM32(lat, lng);
    const snapX = Math.round(obs.x / CACHE_SNAP) * CACHE_SNAP;
    const snapY = Math.round(obs.y / CACHE_SNAP) * CACHE_SNAP;
    const key   = `${snapX},${snapY},${gridRes}`;
    if (key === lastGridKey) return lastGrid;

    const xmin = obs.x - GRID_RADIUS, xmax = obs.x + GRID_RADIUS;
    const ymin = obs.y - GRID_RADIUS, ymax = obs.y + GRID_RADIUS;
    const url  = `${DHM_WCS}?service=WCS&version=1.0.0&request=GetCoverage` +
      `&coverage=dhm_overflade&bbox=${xmin},${ymin},${xmax},${ymax}` +
      `&width=${gridRes}&height=${gridRes}&crs=EPSG:25832&format=GTiff&token=${DHM_TOKEN}`;

    try {
      let resp;
      for (let attempt = 0; attempt < 3; attempt++) {
        resp = await fetch(url);
        if (resp.status !== 504) break;
        await new Promise(r => setTimeout(r, 800 * (attempt + 1)));
      }
      if (!resp.ok) throw new Error(`WCS ${resp.status}`);
      const buf  = await resp.arrayBuffer();
      const tiff = await GeoTIFF.fromArrayBuffer(buf);
      const img  = await tiff.getImage();
      const [rasterData] = await img.readRasters();
      const [bxmin, bymin, bxmax, bymax] = img.getBoundingBox();
      const grid = { rasterData, W: img.getWidth(), H: img.getHeight(),
                     xmin: bxmin, ymin: bymin, xmax: bxmax, ymax: bymax, obsUTM: obs };
      lastGrid    = grid;
      lastGridKey = key;
      return grid;
    } catch (e) {
      console.warn('View3D terrain grid fetch failed:', e);
      lastGrid    = null;
      lastGridKey = key;
      return null;
    }
  }

  // ── Inner hi-res terrain patch ───────────────────────────────────────────────
  async function fetchInnerGrid(lat, lng) {
    if (terrainGridRes() === 0 || !inDenmark(lat, lng)) return null;
    const obs   = latLonToUTM32(lat, lng);
    const snapX = Math.round(obs.x / INNER_SNAP) * INNER_SNAP;
    const snapY = Math.round(obs.y / INNER_SNAP) * INNER_SNAP;
    const key   = `${snapX},${snapY}`;
    if (key === lastInnerKey) return lastInnerGrid;
    const xmin = obs.x - INNER_RADIUS, xmax = obs.x + INNER_RADIUS;
    const ymin = obs.y - INNER_RADIUS, ymax = obs.y + INNER_RADIUS;
    const url  = `${DHM_WCS}?service=WCS&version=1.0.0&request=GetCoverage` +
      `&coverage=dhm_overflade&bbox=${xmin},${ymin},${xmax},${ymax}` +
      `&width=${INNER_RES}&height=${INNER_RES}&crs=EPSG:25832&format=GTiff&token=${DHM_TOKEN}`;
    try {
      let resp;
      for (let attempt = 0; attempt < 3; attempt++) {
        resp = await fetch(url);
        if (resp.status !== 504) break;
        await new Promise(r => setTimeout(r, 800 * (attempt + 1)));
      }
      if (!resp.ok) throw new Error(`WCS ${resp.status}`);
      const buf  = await resp.arrayBuffer();
      const tiff = await GeoTIFF.fromArrayBuffer(buf);
      const img  = await tiff.getImage();
      const [rasterData] = await img.readRasters();
      const [bxmin, bymin, bxmax, bymax] = img.getBoundingBox();
      const grid = { rasterData, W: img.getWidth(), H: img.getHeight(),
                     xmin: bxmin, ymin: bymin, xmax: bxmax, ymax: bymax, obsUTM: obs };
      lastInnerGrid = grid; lastInnerKey = key;
      return grid;
    } catch (e) {
      console.warn('View3D inner grid fetch failed:', e);
      lastInnerGrid = null; lastInnerKey = key;
      return null;
    }
  }

  // ── Terrain mesh ─────────────────────────────────────────────────────────────
  function buildTerrainMesh(grid, zObs) {
    const { rasterData, W, H } = grid;
    const T   = isDayMode ? THEMES.day : THEMES.night;
    const geo = new THREE.PlaneGeometry(GRID_RADIUS * 2, GRID_RADIUS * 2, W - 1, H - 1);
    geo.rotateX(-Math.PI / 2);
    const pos = geo.attributes.position;
    for (let j = 0; j < H; j++) {
      for (let i = 0; i < W; i++) {
        const v = rasterData[j * W + i];
        pos.setY(j * W + i, (!isNaN(v) && v > -100) ? v : zObs);
      }
    }
    pos.needsUpdate = true;
    geo.computeVertexNormals();

    const useSat = isSatelliteMode && satTex;
    const satColor = isDayMode ? 0xffffff : 0x334455;

    if (useSat) {
      // Remap UVs so the SAT_RADIUS coverage maps to the texture centre;
      // beyond SAT_RADIUS the texture clamps to its edge pixels.
      const uv = geo.attributes.uv;
      const scale = GRID_RADIUS / SAT_RADIUS;
      for (let k = 0; k < uv.count; k++) {
        uv.setXY(k,
          0.5 + (uv.getX(k) - 0.5) * scale,
          0.5 + (uv.getY(k) - 0.5) * scale,
        );
      }
      uv.needsUpdate = true;
    }

    // polygonOffset pushes outer mesh back so the inner hi-res patch renders on top
    const meshes = [new THREE.Mesh(geo, useSat
      ? new THREE.MeshBasicMaterial({ map: satTex, color: satColor, polygonOffset: true, polygonOffsetFactor: 2, polygonOffsetUnits: 2 })
      : new THREE.MeshLambertMaterial({ color: T.terrain, side: THREE.DoubleSide, polygonOffset: true, polygonOffsetFactor: 2, polygonOffsetUnits: 2 })
    )];
    if (!useSat) {
      meshes.push(new THREE.Mesh(geo, new THREE.MeshBasicMaterial({
        color: T.terrainWf, wireframe: true, opacity: 0.15, transparent: true,
      })));
    }
    return meshes;
  }

  // ── Inner hi-res terrain mesh (1 km centre patch) ────────────────────────────
  function buildInnerMesh(innerGrid, zObs) {
    const { rasterData, W, H } = innerGrid;
    const T   = isDayMode ? THEMES.day : THEMES.night;
    const geo = new THREE.PlaneGeometry(INNER_RADIUS * 2, INNER_RADIUS * 2, W - 1, H - 1);
    geo.rotateX(-Math.PI / 2);
    const pos = geo.attributes.position;
    for (let j = 0; j < H; j++) {
      for (let i = 0; i < W; i++) {
        const v = rasterData[j * W + i];
        pos.setY(j * W + i, (!isNaN(v) && v > -100) ? v : zObs);
      }
    }
    pos.needsUpdate = true;
    geo.computeVertexNormals();

    const useSat = isSatelliteMode && satTex;
    const satColor = isDayMode ? 0xffffff : 0x334455;

    if (useSat) {
      // Remap UVs to sample the centre region of the satellite texture
      const uv = geo.attributes.uv;
      const ratio = INNER_RADIUS / SAT_RADIUS;
      for (let k = 0; k < uv.count; k++) {
        uv.setXY(k,
          0.5 + (uv.getX(k) - 0.5) * ratio,
          0.5 + (uv.getY(k) - 0.5) * ratio,
        );
      }
      uv.needsUpdate = true;
    }

    const meshes = [new THREE.Mesh(geo, useSat
      ? new THREE.MeshBasicMaterial({ map: satTex, color: satColor })
      : new THREE.MeshLambertMaterial({ color: T.terrain, side: THREE.DoubleSide })
    )];
    if (!useSat) {
      meshes.push(new THREE.Mesh(geo, new THREE.MeshBasicMaterial({
        color: T.terrainWf, wireframe: true, opacity: 0.25, transparent: true,
      })));
    }
    return meshes;
  }

  // ── Flat satellite tile (no elevation data) ───────────────────────────────────
  function buildFlatSatTile(zObs) {
    const geo = new THREE.PlaneGeometry(SAT_RADIUS * 2, SAT_RADIUS * 2);
    geo.rotateX(-Math.PI / 2);
    const satColor = isDayMode ? 0xffffff : 0x334455;
    const mesh = new THREE.Mesh(geo, new THREE.MeshBasicMaterial({ map: satTex, color: satColor }));
    mesh.position.y = zObs + 0.5;
    return mesh;
  }

  // ── Sky dome ─────────────────────────────────────────────────────────────────
  function buildSky() {
    const isDay = isDayMode;
    const mat = new THREE.ShaderMaterial({
      side: THREE.BackSide,
      depthWrite: false,
      uniforms: {
        uZenith:  { value: new THREE.Color(isDay ? 0x0d4b9c : 0x030810) },
        uHorizon: { value: new THREE.Color(isDay ? 0x87ceeb : 0x1e3a5a) },
        uIsDay:   { value: isDay ? 1.0 : 0.0 },
      },
      vertexShader: `
        varying vec3 vDir;
        void main() {
          vDir = normalize(position);
          gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
        }
      `,
      fragmentShader: `
        varying vec3 vDir;
        uniform vec3  uZenith;
        uniform vec3  uHorizon;
        uniform float uIsDay;

        float hash(vec2 p) { return fract(sin(dot(p, vec2(127.1,311.7))) * 43758.5453); }
        float vnoise(vec2 p) {
          vec2 i = floor(p), f = fract(p);
          f = f * f * (3.0 - 2.0 * f);
          return mix(mix(hash(i), hash(i+vec2(1,0)), f.x),
                     mix(hash(i+vec2(0,1)), hash(i+vec2(1,1)), f.x), f.y);
        }
        float fbm(vec2 p) {
          return vnoise(p)*0.5 + vnoise(p*2.1)*0.3 + vnoise(p*4.3)*0.2;
        }

        void main() {
          vec3 dir = normalize(vDir);
          float t = clamp(dir.y, 0.0, 1.0);
          vec3 col = mix(uHorizon, uZenith, pow(t, 0.6));

          if (uIsDay > 0.5) {
            if (dir.y > 0.0) {
              // Project onto cloud layer plane; offset to break zenith symmetry
              vec2 uv = dir.xz / (dir.y + 0.2) + vec2(1.3, 2.1);
              float cloud = fbm(uv * 0.8);
              cloud = smoothstep(0.42, 0.66, cloud);
              float fade = smoothstep(0.0, 0.08, dir.y) * (1.0 - smoothstep(0.75, 0.95, dir.y));
              cloud *= fade;
              // Bright top, slightly blue-grey underside
              vec3 cloudCol = mix(vec3(0.72, 0.76, 0.82), vec3(0.97, 0.97, 1.0), cloud);
              col = mix(col, cloudCol, cloud * 0.88);
            }
          }

          gl_FragColor = vec4(col, 1.0);
        }
      `,
    });
    return new THREE.Mesh(new THREE.SphereGeometry(2e6, 32, 16), mat);
  }

  // ── Scene build ──────────────────────────────────────────────────────────────
  function buildScene(results, observer, obsElev, R, gridData, innerGridData) {
    scene.clear();

    const overlay = document.getElementById('view3d-overlay');
    const hasResults = results && results.length > 0;
    if (!hasResults) {
      overlay.textContent = !lastObserver
        ? 'Place an observer on the map'
        : 'Loading…';
      overlay.style.display = 'flex';
      return;
    }
    overlay.style.display = 'none';

    const T = isDayMode ? THEMES.day : THEMES.night;

    // Lights
    scene.add(new THREE.HemisphereLight(T.hemiSky, T.hemiGnd, T.hemiInt));
    const sun = new THREE.DirectionalLight(T.sunColor, T.sunInt);
    sun.position.set(...T.sunPos).normalize();
    scene.add(sun);

    // Observer ground elevation — prefer inner grid (more accurate for observer position)
    function lookupZ(g) {
      const { rasterData, W, H, xmin, ymin, xmax, ymax, obsUTM } = g;
      const col = Math.round((obsUTM.x - xmin) / (xmax - xmin) * (W - 1));
      const row = Math.round((ymax - obsUTM.y) / (ymax - ymin) * (H - 1));
      const v   = rasterData[Math.max(0, Math.min(H - 1, row)) * W + Math.max(0, Math.min(W - 1, col))];
      return (!isNaN(v) && v > -100) ? v : null;
    }
    const zObs = (innerGridData && lookupZ(innerGridData))
      ?? (gridData && lookupZ(gridData))
      ?? (results.find(r => r.terrain)?.terrain.zObs ?? 0);

    const eyeY = zObs + obsElev;
    camera.position.set(0, eyeY, 0);

    if (!userHasDragged) {
      yaw   = results[0].bearing * Math.PI / 180;
      pitch = 0;
    }
    applyCameraRotation();

    // Sky dome
    scene.add(buildSky());

    // Large flat ground (fills areas outside the 5km tile)
    const groundGeo = new THREE.PlaneGeometry(4e6, 4e6);
    groundGeo.rotateX(-Math.PI / 2);
    scene.add(new THREE.Mesh(groundGeo, new THREE.MeshLambertMaterial({ color: T.ground })));

    // Terrain tile: outer coarse mesh, then inner hi-res patch on top
    const useGrid = terrainGridRes() > 0 ? gridData : null;
    if (useGrid) {
      buildTerrainMesh(useGrid, zObs).forEach(m => scene.add(m));
      if (innerGridData) buildInnerMesh(innerGridData, zObs).forEach(m => scene.add(m));
    } else if (isSatelliteMode && satTex) {
      scene.add(buildFlatSatTile(zObs));
    }

    // Observer post
    const postH   = Math.max(obsElev, 0.5);
    const postGeo = new THREE.CylinderGeometry(0.12, 0.12, postH, 6);
    postGeo.translate(0, zObs + postH / 2, 0);
    scene.add(new THREE.Mesh(postGeo, new THREE.MeshLambertMaterial({ color: 0x60a5fa })));
    const eyeGeo = new THREE.SphereGeometry(0.35, 8, 8);
    eyeGeo.translate(0, eyeY, 0);
    scene.add(new THREE.Mesh(eyeGeo, new THREE.MeshBasicMaterial({ color: 0xffffff })));

    // Targets
    results.forEach(r => {
      const { t, distM, bearing, vis, terrain } = r;
      const zTgt   = terrain?.zTgt ?? 0;
      const tgtMSL = zTgt + t.elev;
      const color  = new THREE.Color(t.color);
      const tgtPos = toWorld(distM, bearing, tgtMSL);
      const sR     = Math.max(distM * 0.004, 3);

      const sphereMesh = new THREE.Mesh(
        new THREE.SphereGeometry(sR, 12, 8),
        new THREE.MeshLambertMaterial({ color, emissive: color, emissiveIntensity: 0.7 })
      );
      sphereMesh.position.copy(tgtPos);
      scene.add(sphereMesh);

      const halo = new THREE.Mesh(
        new THREE.SphereGeometry(sR * 2.4, 12, 8),
        new THREE.MeshBasicMaterial({ color, transparent: true, opacity: 0.1, side: THREE.BackSide })
      );
      halo.position.copy(tgtPos);
      scene.add(halo);

      const pl = new THREE.PointLight(color, 2.0, Math.max(sR * 60, 500));
      pl.position.copy(tgtPos);
      scene.add(pl);


      const lineGeo = new THREE.BufferGeometry().setFromPoints([
        new THREE.Vector3(0, eyeY, 0), tgtPos,
      ]);
      scene.add(new THREE.Line(lineGeo,
        new THREE.LineBasicMaterial({ color, transparent: true, opacity: 0.3 })));
    });
  }

  // ── Camera control ───────────────────────────────────────────────────────────
  function applyCameraRotation() {
    pitch = Math.max(-Math.PI / 2 + 0.01, Math.min(Math.PI / 2 - 0.01, pitch));
    const qYaw   = new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(0, 1, 0), -yaw);
    const qPitch = new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(1, 0, 0), pitch);
    camera.quaternion.copy(qYaw).multiply(qPitch);
  }

  function bindPointerEvents(canvas) {
    canvas.addEventListener('pointerdown', e => {
      isPointerDown = true;
      lastPX = e.clientX; lastPY = e.clientY;
      canvas.setPointerCapture(e.pointerId);
    });
    canvas.addEventListener('pointermove', e => {
      if (!isPointerDown) return;
      yaw   += (e.clientX - lastPX) * 0.004;
      pitch += (e.clientY - lastPY) * 0.004;
      lastPX = e.clientX; lastPY = e.clientY;
      applyCameraRotation();
      userHasDragged = true;
    });
    canvas.addEventListener('pointerup',     () => { isPointerDown = false; });
    canvas.addEventListener('pointercancel', () => { isPointerDown = false; });
  }

  // ── Render loop ──────────────────────────────────────────────────────────────
  function startRenderLoop() {
    if (animId) return;
    function frame() {
      animId = requestAnimationFrame(frame);
      renderer.render(scene, camera);
    }
    frame();
  }

  // ── Public API ───────────────────────────────────────────────────────────────
  function update(results, observer, obsElev, R) {
    if (!initialized) init();
    lastResults = results; lastObserver = observer; lastObsElev = obsElev; lastR = R;

    resize();
    buildScene(results, observer, obsElev, R, lastGrid, lastInnerGrid);
    startRenderLoop();

    if (!observer || !results || !results.length) return;

    // Outer terrain grid
    const gridRes = terrainGridRes();
    if (gridRes > 0) {
      const obs   = latLonToUTM32(observer.lat, observer.lng);
      const snapX = Math.round(obs.x / CACHE_SNAP) * CACHE_SNAP;
      const snapY = Math.round(obs.y / CACHE_SNAP) * CACHE_SNAP;
      const key   = `${snapX},${snapY},${gridRes}`;
      if (key !== lastGridKey && !pendingGridFetch) {
        pendingGridFetch = true;
        fetchTerrainGrid(observer.lat, observer.lng).then(grid => {
          pendingGridFetch = false;
          if (lastObserver === observer) buildScene(lastResults, lastObserver, lastObsElev, lastR, grid, lastInnerGrid);
        });
      }

      // Inner hi-res patch
      const obsUTM = latLonToUTM32(observer.lat, observer.lng);
      const iSnapX = Math.round(obsUTM.x / INNER_SNAP) * INNER_SNAP;
      const iSnapY = Math.round(obsUTM.y / INNER_SNAP) * INNER_SNAP;
      const iKey   = `${iSnapX},${iSnapY}`;
      if (iKey !== lastInnerKey && !pendingInnerFetch) {
        pendingInnerFetch = true;
        fetchInnerGrid(observer.lat, observer.lng).then(inner => {
          pendingInnerFetch = false;
          if (lastObserver === observer) buildScene(lastResults, lastObserver, lastObsElev, lastR, lastGrid, inner);
        });
      }
    }

    // Satellite texture
    if (isSatelliteMode) triggerSatFetch(observer);
  }

  function setSatellite(enabled) {
    isSatelliteMode = enabled;
    if (enabled && lastObserver) {
      triggerSatFetch(lastObserver);
    }
    rebuildScene();
  }

  function resize() {
    // When switching to 3D with existing results, show Loading… until the scene renders
    const _ov = document.getElementById('view3d-overlay');
    if (_ov && _ov.style.display !== 'none') {
      _ov.textContent = !lastObserver
        ? 'Place an observer on the map'
        : 'Loading…';
    }
    if (!renderer) return;
    const container = document.getElementById('view3d-container');
    const w = container.offsetWidth, h = container.offsetHeight;
    if (w === 0 || h === 0) return;
    renderer.setSize(w, h, false);
    if (camera) { camera.aspect = w / h; camera.updateProjectionMatrix(); }
  }

  window.View3D = { update, resize, setSatellite };

})();
