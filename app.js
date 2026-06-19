// ─── WGS84 ───────────────────────────────────────────────────────────────────
const WGS84 = { a: 6378137.0, b: 6356752.314245, f: 1/298.257223563, e2: 6.69437999014e-3 };

function earthRadiusAt(latDeg) {
  const φ = latDeg * Math.PI / 180, { a, e2 } = WGS84;
  const s = Math.sin(φ), d = 1 - e2 * s * s;
  return Math.sqrt(a*(1-e2)/Math.pow(d,1.5) * a/Math.sqrt(d));
}

// ─── Vincenty ────────────────────────────────────────────────────────────────
function vincenty(lat1, lon1, lat2, lon2) {
  const { a, b, f } = WGS84;
  const φ1 = lat1*Math.PI/180, φ2 = lat2*Math.PI/180, L = (lon2-lon1)*Math.PI/180;
  const U1 = Math.atan((1-f)*Math.tan(φ1)), U2 = Math.atan((1-f)*Math.tan(φ2));
  const sU1=Math.sin(U1),cU1=Math.cos(U1),sU2=Math.sin(U2),cU2=Math.cos(U2);
  let λ=L, λP, iter=0, sσ,cσ,σ,sα,c2α,c2σm,C;
  do {
    const sλ=Math.sin(λ),cλ=Math.cos(λ);
    sσ=Math.sqrt((cU2*sλ)**2+(cU1*sU2-sU1*cU2*cλ)**2);
    if(sσ===0)return 0;
    cσ=sU1*sU2+cU1*cU2*cλ; σ=Math.atan2(sσ,cσ);
    sα=(cU1*cU2*sλ)/sσ; c2α=1-sα**2;
    c2σm=c2α?cσ-2*sU1*sU2/c2α:0;
    C=(f/16)*c2α*(4+f*(4-3*c2α)); λP=λ;
    λ=L+(1-C)*f*sα*(σ+C*sσ*(c2σm+C*cσ*(-1+2*c2σm**2)));
  } while(Math.abs(λ-λP)>1e-12&&++iter<200);
  const u2=c2α*(a**2-b**2)/b**2;
  const A=1+u2/16384*(4096+u2*(-768+u2*(320-175*u2)));
  const B=u2/1024*(256+u2*(-128+u2*(74-47*u2)));
  const Δσ=B*sσ*(c2σm+B/4*(cσ*(-1+2*c2σm**2)-B/6*c2σm*(-3+4*sσ**2)*(-3+4*c2σm**2)));
  return b*A*(σ-Δσ);
}

// ─── Core geometry ───────────────────────────────────────────────────────────
function calcVisibility(h_o, h_t, distM, R) {
  const D_obs = Math.sqrt(2*R*h_o);
  const D_tgt = Math.sqrt(2*R*h_t);
  const h_min = Math.max(0, Math.pow(Math.max(0, distM-D_obs)/Math.sqrt(2*R), 2));
  const hidden  = Math.min(h_t, h_min);
  const visible = Math.max(0, h_t - h_min);
  const drop    = distM*distM/(2*R);
  const elevDeg = (h_t - drop + h_o) / distM * 180/Math.PI;
  return { D_obs, D_tgt, h_min, hidden, visible, elevDeg };
}

// ─── State ───────────────────────────────────────────────────────────────────
const TARGET_COLORS = ['#f59e0b','#34d399','#f472b6','#a78bfa','#fb923c','#38bdf8'];
let observer = null, obsMarker = null, obsElev = 2;
let targets = [], nextId = 1, placingObs = false, placingTgt = false;
let refractionK = 0.13;

// ─── Fragment state ──────────────────────────────────────────────────────────
function r5(n) { return Math.round(n * 1e5) / 1e5; }

function b64enc(s) { return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, ''); }
function b64dec(s) { return atob(s.replace(/-/g, '+').replace(/_/g, '/')); }

function decodeFragment() {
  try {
    if (location.hash.length < 2) return null;
    return JSON.parse(b64dec(location.hash.slice(1)));
  } catch(e) { return null; }
}

function encodeFragment() {
  const state = {};
  const c = map.getCenter();
  state.c = [r5(c.lat), r5(c.lng), map.getZoom()];
  if (observer) state.o = [r5(observer.lat), r5(observer.lng), obsElev];
  if (refractionK !== 0.13) state.k = refractionK;
  if (targets.length) state.t = targets.map(t => {
    const row = [r5(t.lat), r5(t.lng), t.elev];
    if (t.dim) row.push(t.dim);
    return row;
  });
  history.replaceState(null, '', '#' + b64enc(JSON.stringify(state)));
}

// ─── Map ─────────────────────────────────────────────────────────────────────
const _saved = decodeFragment();
const _initCenter = _saved?.c ? [_saved.c[0], _saved.c[1]] : [55.6761, 12.5683];
const _initZoom   = _saved?.c ? _saved.c[2] : 7;

const map = L.map('map', { center: _initCenter, zoom: _initZoom, zoomControl: false });
L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
  attribution: '© <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>',
  maxZoom: 19,
}).addTo(map);
L.control.zoom({ position: 'bottomright' }).addTo(map);

map.on('moveend', encodeFragment);

// ─── Markers ─────────────────────────────────────────────────────────────────
function makeObsIcon() {
  return L.divIcon({
    html: `<div style="width:18px;height:18px;background:#60a5fa;border:2px solid #fff;border-radius:50%;box-shadow:0 0 0 3px rgba(96,165,250,0.4)"></div>`,
    iconAnchor: [9,9], className: '',
  });
}
function makeTgtIcon(color) {
  return L.divIcon({
    html: `<div style="width:14px;height:14px;background:${color};border:2px solid #fff;border-radius:2px;box-shadow:0 0 0 3px ${color}55;transform:rotate(45deg)"></div>`,
    iconAnchor: [7,7], className: '',
  });
}

// ─── Click handler ───────────────────────────────────────────────────────────
map.on('click', e => {
  if (!observer || placingObs) { placeObserver(e.latlng); }
  else if (placingTgt) { placingTgt = false; addTarget(e.latlng); }
  updateHint();
});

function placeObserver(latlng) {
  observer = latlng;
  if (obsMarker) map.removeLayer(obsMarker);
  obsMarker = L.marker(latlng, { icon: makeObsIcon(), draggable: true, zIndexOffset: 100 })
    .addTo(map)
    .bindTooltip('Observer', { permanent: false });
  obsMarker.on('drag', () => { observer = obsMarker.getLatLng(); refreshLines(); compute(); });
  placingObs = false;
  refreshLines(); compute();
}

function addTarget(latlng, elev, dim) {
  const id = nextId++;
  const color = TARGET_COLORS[targets.length % TARGET_COLORS.length];
  const e = elev !== undefined ? elev : 30;
  const d = dim || 0;
  const marker = L.marker(latlng, { icon: makeTgtIcon(color), draggable: true })
    .addTo(map);
  const t = { id, lat: latlng.lat, lng: latlng.lng, elev: e, dim: d, color, marker, line: null, labelMarker: null };
  targets.push(t);
  marker.on('drag', () => { t.lat = marker.getLatLng().lat; t.lng = marker.getLatLng().lng; refreshLines(); compute(); });
  refreshLines(); compute();
}

function removeTarget(id) {
  const idx = targets.findIndex(t => t.id === id);
  if (idx === -1) return;
  const t = targets[idx];
  if (t.marker) map.removeLayer(t.marker);
  if (t.line) map.removeLayer(t.line);
  if (t.labelMarker) map.removeLayer(t.labelMarker);
  targets.splice(idx, 1);
  compute();
}

function refreshLines() {
  targets.forEach(t => {
    if (t.line) { map.removeLayer(t.line); t.line = null; }
    if (t.labelMarker) { map.removeLayer(t.labelMarker); t.labelMarker = null; }
    if (!observer) return;
    t.line = L.polyline([[observer.lat,observer.lng],[t.lat,t.lng]], {
      color: t.color, weight: 2, dashArray: '6 5', opacity: 0.85,
    }).addTo(map);
    const distM = vincenty(observer.lat, observer.lng, t.lat, t.lng);
    const distStr = distM < 1000 ? `${distM.toFixed(0)} m` : `${(distM/1000).toFixed(1)} km`;
    t.labelMarker = L.marker([(observer.lat+t.lat)/2,(observer.lng+t.lng)/2], {
      icon: L.divIcon({
        html: `<div style="display:inline-block;white-space:nowrap;transform:translateX(-50%);background:rgba(15,17,23,0.88);border:1px solid #2d3149;border-radius:4px;padding:2px 7px;font-size:11px;color:#e2e8f0;font-family:system-ui,sans-serif">${distStr}</div>`,
        className: '', iconAnchor: [0,10],
      }),
      interactive: false,
    }).addTo(map);
  });
}

// ─── Controls ────────────────────────────────────────────────────────────────
document.getElementById('btn-add-target').addEventListener('click', () => {
  if (!observer) { updateHint('Click map to place Observer first'); return; }
  placingTgt = true;
  updateHint('Click map to place Target');
});
document.getElementById('obs-elev').addEventListener('input', () => { obsElev = parseFloat(document.getElementById('obs-elev').value)||0; compute(); });
document.getElementById('refraction-preset').addEventListener('change', e => { refractionK = parseFloat(e.target.value); compute(); });

function updateHint(msg) {
  const el = document.getElementById('map-hint');
  if (msg) { el.textContent = msg; el.style.display = ''; return; }
  if (!observer) { el.textContent = 'Click map to place Observer'; el.style.display = ''; }
  else if (placingTgt) { el.textContent = 'Click map to place Target'; el.style.display = ''; }
  else el.style.display = 'none';
}

// ─── Sidebar ─────────────────────────────────────────────────────────────────
function fmt(m) {
  if (m === null || m === undefined || isNaN(m)) return '—';
  if (Math.abs(m) >= 1e6) return `${(m/1e6).toFixed(1)} Mm`;
  if (Math.abs(m) >= 1000) return `${(m/1000).toFixed(1)} km`;
  return `${Math.round(m)} m`;
}
function fmtDeg(d) {
  if (isNaN(d)) return '—';
  const abs = Math.abs(d);
  if (abs < 0.01) return `${d.toFixed(3)}°`;
  if (abs < 1)    return `${d.toFixed(2)}°`;
  return `${d.toFixed(1)}°`;
}

function statsHTML(r) {
  const { t, distM, vis } = r;
  const objSize  = t.dim > 0 ? t.dim : null;
  const elevMm   = Math.round(Math.tan(vis.elevDeg * Math.PI / 180) * 1000);
  const refMm    = (objSize && distM > 0) ? Math.round(objSize / distM * 1000) : null;
  const visClass = vis.visible === 0 ? 'bad' : vis.hidden > 0 ? 'warn' : 'good';
  const visText  = vis.visible === 0 ? 'Hidden' : vis.hidden > 0 ? 'Partial' : 'Full view';
  const hidden_pct  = t.elev > 0 ? `${(vis.hidden / t.elev * 100).toFixed(0)}%` : '0%';
  const visible_pct = t.elev > 0 ? `${(vis.visible / t.elev * 100).toFixed(0)}%` : '100%';
  return `
    <div class="stat-item stat-full">
      <div class="stat-name">Distance</div>
      <div class="stat-val">${fmt(distM)} <span class="stat-val ${visClass}" style="font-size:11px">${visText}</span></div>
    </div>
    <div class="stat-item">
      <div class="stat-name">Observer horizon</div>
      <div class="stat-val">${fmt(vis.D_obs)}</div>
    </div>
    <div class="stat-item">
      <div class="stat-name">Target horizon</div>
      <div class="stat-val">${fmt(vis.D_tgt)}</div>
    </div>
    <div class="stat-item">
      <div class="stat-name">Min visible ht</div>
      <div class="stat-val">${fmt(vis.h_min)}</div>
    </div>
    <div class="stat-item">
      <div class="stat-name">Hidden</div>
      <div class="stat-val ${vis.hidden > 0 ? 'warn' : 'good'}">${fmt(vis.hidden)} (${hidden_pct})</div>
    </div>
    <div class="stat-item">
      <div class="stat-name">Visible</div>
      <div class="stat-val">${fmt(vis.visible)} (${visible_pct})</div>
    </div>
    <div class="stat-item">
      <div class="stat-name">Elev above horiz</div>
      <div class="stat-val">${fmtDeg(vis.elevDeg)}</div>
    </div>
    <div class="stat-item">
      <div class="stat-name">Apparent size @ 1 m</div>
      <div class="stat-val">${elevMm} mm over horizon${refMm !== null ? ` · ${refMm} mm wide (ref)` : ''}</div>
    </div>
  `;
}

function renderSidebar(results) {
  const empty = document.getElementById('sidebar-empty');
  const cardsEl = document.getElementById('target-cards');

  if (!results || results.length === 0) {
    empty.style.display = '';
    cardsEl.innerHTML = '';
    return;
  }
  empty.style.display = 'none';

  // Rebuild card shells only when the target list changes (add/remove)
  const currentIds = [...cardsEl.querySelectorAll('.tgt-card')].map(c => c.dataset.id).join(',');
  const newIds = results.map(r => String(r.t.id)).join(',');
  if (currentIds !== newIds) {
    cardsEl.innerHTML = '';
    results.forEach((r, i) => {
      const { t } = r;
      const card = document.createElement('div');
      card.className = 'tgt-card';
      card.dataset.id = t.id;
      card.style.borderTop = `2px solid ${t.color}`;
      card.innerHTML = `
        <div class="tgt-card-header">
          <div class="tgt-color-dot" style="background:${t.color}"></div>
          <div class="tgt-name" style="color:${t.color}">Target ${i + 1}</div>
          <button class="tgt-remove" onclick="removeTarget(${t.id})">×</button>
        </div>
        <div class="tgt-inputs">
          <div class="tgt-input-cell">
            <div class="tgt-input-label">Top elevation</div>
            <div class="tgt-input-row">
              <input class="elev-input" type="number" value="${t.elev}" min="0" max="30000" step="1"
                data-id="${t.id}" data-field="elev" oninput="onTargetElev(this)">
              <span class="elev-unit">m ASL</span>
            </div>
          </div>
          <div class="tgt-input-cell">
            <div class="tgt-input-label">Ref. dimension</div>
            <div class="tgt-input-row">
              <input class="elev-input" type="number" value="${t.dim || ''}" min="0" max="100000" step="1"
                placeholder="—" data-id="${t.id}" data-field="dim" oninput="onTargetDim(this)"
                style="color:${t.dim ? '#e2e8f0' : '#334155'}">
              <span class="elev-unit">m</span>
            </div>
          </div>
        </div>
        <div class="tgt-stats" data-id="${t.id}"></div>
      `;
      cardsEl.appendChild(card);
    });
  }

  // Always update stats in-place — never touches the input elements
  results.forEach(r => {
    const statsEl = cardsEl.querySelector(`.tgt-stats[data-id="${r.t.id}"]`);
    if (statsEl) statsEl.innerHTML = statsHTML(r);
  });
}

function onTargetElev(el) {
  const t = targets.find(x => x.id === parseInt(el.dataset.id));
  if (t) { t.elev = parseFloat(el.value)||0; compute(); }
}
function onTargetDim(el) {
  const t = targets.find(x => x.id === parseInt(el.dataset.id));
  if (t) {
    t.dim = parseFloat(el.value)||0;
    el.style.color = t.dim ? '#e2e8f0' : '#334155';
    compute();
  }
}

// ─── Compute ─────────────────────────────────────────────────────────────────
function compute() {
  obsElev = parseFloat(document.getElementById('obs-elev').value)||0;
  const hasData = observer && targets.length > 0;

  if (!hasData) { renderSidebar(null); drawDiagram(null); return; }

  const R_geom = earthRadiusAt(observer.lat);
  const k = refractionK;
  const R = R_geom / (1-k);

  const results = targets.map(t => {
    const distM = vincenty(observer.lat, observer.lng, t.lat, t.lng);
    const vis = calcVisibility(obsElev, t.elev, distM, R);
    return { t, distM, vis };
  });

  renderSidebar(results);
  drawDiagram(results, R);
  encodeFragment();
}

// ─── Diagram ─────────────────────────────────────────────────────────────────
function drawDiagram(results, R_eff) {
  const canvas = document.getElementById('diagram-canvas');
  const dpr = window.devicePixelRatio || 1;
  const W = canvas.offsetWidth, H = canvas.offsetHeight;
  if (W === 0 || H === 0) return;
  canvas.width = W*dpr; canvas.height = H*dpr;
  const ctx = canvas.getContext('2d');
  ctx.scale(dpr, dpr);
  ctx.clearRect(0, 0, W, H);

  if (!results || results.length === 0) {
    ctx.fillStyle = '#1e2133';
    ctx.font = '11px system-ui';
    ctx.textAlign = 'center';
    ctx.fillText('Place observer and targets on the map', W/2, H/2);
    return;
  }

  const R = R_eff;

  // Chord frame: both surface endpoints at y=0, Earth humps upward between them.
  // earth_y(x) = x*(maxDist-x)/(2R)  — parabolic sagitta above chord.
  const maxDist = Math.max(...results.map(r => r.distM));
  const earth_y = x => x * (maxDist - x) / (2 * R);
  const peakBulge = maxDist * maxDist / (8 * R); // midpoint hump height

  // maxH: accommodate observer elevation, all target tops above their chord-frame surface,
  // all h_min values above their chord-frame surface, and the midpoint bulge itself.
  const maxH = Math.max(
    obsElev,                                               // observer above chord at x=0
    peakBulge,                                             // hump itself
    ...results.map(r => earth_y(r.distM) + r.t.elev),     // target tops
    ...results.map(r => earth_y(r.distM) + r.vis.h_min),  // h_min points
    1
  ) * 1.4;

  const pad = { l: 20, r: 20, t: 16, b: 10 };
  const plotW = W - pad.l - pad.r;
  const plotH = H - pad.t - pad.b;
  // Horizontal inset: keep curve endpoints away from left/right edges
  const hInset = plotW * 0.06;
  const px = x => pad.l + hInset + x/maxDist * (plotW - 2*hInset);
  // Vertical padding below y=0 (chord baseline) so endpoints don't sit at canvas bottom
  const yBelowPad = maxH * 0.12;
  const yRange = maxH + yBelowPad;
  const py = y => pad.t + plotH - (y + yBelowPad) / yRange * plotH;

  // Sky — fill full canvas so no strips show through at edges
  const sky = ctx.createLinearGradient(0, 0, 0, H);
  sky.addColorStop(0, '#071020'); sky.addColorStop(1, '#0c1a30');
  ctx.fillStyle = sky;
  ctx.fillRect(0, 0, W, H);

  // Arc extends from canvas left edge to right edge (beyond hInset padding)
  const steps = 300;
  const extraX_l = (pad.l + hInset) * maxDist / (plotW - 2 * hInset);
  const extraX_r = (pad.r + hInset) * maxDist / (plotW - 2 * hInset);
  const xL = -extraX_l, xR = maxDist + extraX_r;

  function drawEarthArc(close) {
    ctx.beginPath();
    for (let i = 0; i <= steps; i++) {
      const x = xL + i/steps * (xR - xL), y = earth_y(x);
      i === 0 ? ctx.moveTo(px(x), py(y)) : ctx.lineTo(px(x), py(y));
    }
    if (close) { ctx.lineTo(W, H); ctx.lineTo(0, H); ctx.closePath(); }
  }

  // Earth fill — close at full canvas bottom
  drawEarthArc(true);
  const eg = ctx.createLinearGradient(0, pad.t + plotH*0.4, 0, H);
  eg.addColorStop(0, '#182840'); eg.addColorStop(1, '#0c1828');
  ctx.fillStyle = eg; ctx.fill();

  // Hatching inside the Earth
  ctx.save();
  drawEarthArc(true);
  ctx.clip();
  ctx.strokeStyle = 'rgba(60,100,160,0.18)';
  ctx.lineWidth = 1;
  const hs = 10;
  const hx0 = 0, hx1 = W, hy0 = py(peakBulge), hy1 = H;
  for (let s = hx0 - (hy1 - hy0); s < hx1 + (hy1 - hy0); s += hs) {
    ctx.beginPath();
    ctx.moveTo(s, hy1);
    ctx.lineTo(s + (hy1 - hy0), hy0);
    ctx.stroke();
  }
  ctx.restore();

  // Earth surface line — also extended into inset zones
  drawEarthArc(false);
  ctx.strokeStyle = '#3a5a90'; ctx.lineWidth = 1.5; ctx.stroke();

  // Observer post — surface is at chord level (y=0) at x=0
  const obs_earth = 0;
  const obs_top   = obsElev;
  ctx.beginPath();
  ctx.moveTo(px(0), py(obs_earth)); ctx.lineTo(px(0), py(obs_top));
  ctx.strokeStyle = '#60a5fa'; ctx.lineWidth = 3; ctx.lineCap = 'round'; ctx.stroke(); ctx.lineCap = 'butt';
  ctx.beginPath(); ctx.arc(px(0), py(obs_top), 4, 0, Math.PI*2);
  ctx.fillStyle = '#60a5fa'; ctx.fill();
  ctx.fillStyle = '#93c5fd'; ctx.font = 'bold 9px system-ui'; ctx.textAlign = 'left';
  ctx.fillText('Obs', px(0)+7, py(obs_top)-3);

  // Observer horizon tangent point
  const D_obs = Math.sqrt(2*R*obsElev);
  if (D_obs < maxDist) {
    const hy = earth_y(D_obs);
    ctx.beginPath(); ctx.arc(px(D_obs), py(hy), 3, 0, Math.PI*2);
    ctx.fillStyle = '#fbbf2488'; ctx.fill();
  }

  // Each target
  const barW = Math.max(5, Math.min(10, plotW / results.length / 8));
  results.forEach((r, i) => {
    const { t, distM, vis } = r;
    // In chord frame: target's surface is at earth_y(distM) above the chord baseline
    const tgt_earth = earth_y(distM); // = 0 for the longest target, > 0 for closer ones
    const tgt_top   = tgt_earth + t.elev;
    const tgt_min   = tgt_earth + vis.h_min;

    // Lines and triangle terminate at the left edge of the target bar
    const tgtX = px(distM) - barW;

    // Triangle fill and solid line to top: only when target has height and top is above horizon
    if (vis.visible > 0 && t.elev > 0) {
      ctx.beginPath();
      ctx.moveTo(px(0), py(obs_top));
      ctx.lineTo(tgtX, py(tgt_top));
      ctx.lineTo(tgtX, py(tgt_min));
      ctx.closePath();
      ctx.fillStyle = t.color + '18';
      ctx.fill();

      ctx.beginPath();
      ctx.moveTo(px(0), py(obs_top));
      ctx.lineTo(tgtX, py(tgt_top));
      ctx.strokeStyle = t.color + 'aa';
      ctx.lineWidth = 1.5;
      ctx.stroke();
    }

    // Line of sight to horizon cutoff (dashed)
    ctx.beginPath();
    ctx.moveTo(px(0), py(obs_top));
    ctx.lineTo(tgtX, py(tgt_min));
    ctx.strokeStyle = t.color + '70';
    ctx.lineWidth = 1.5;
    ctx.setLineDash([5,4]); ctx.stroke(); ctx.setLineDash([]);

    // Hidden bar
    if (vis.h_min > 0 && t.elev > 0) {
      const topY = Math.min(tgt_min, tgt_top);
      ctx.fillStyle = '#7f1d1d80';
      ctx.fillRect(px(distM)-barW, py(topY), barW*2, py(tgt_earth)-py(topY));
      ctx.strokeStyle = '#f8717190'; ctx.lineWidth = 1;
      ctx.strokeRect(px(distM)-barW, py(topY), barW*2, py(tgt_earth)-py(topY));
    }

    // Visible bar
    if (vis.visible > 0) {
      ctx.fillStyle = t.color + '44';
      ctx.fillRect(px(distM)-barW, py(tgt_top), barW*2, py(tgt_min)-py(tgt_top));
      ctx.strokeStyle = t.color; ctx.lineWidth = 2;
      ctx.strokeRect(px(distM)-barW, py(tgt_top), barW*2, py(tgt_min)-py(tgt_top));
    } else if (t.elev > 0) {
      ctx.fillStyle = '#7f1d1daa';
      ctx.fillRect(px(distM)-barW, py(tgt_top), barW*2, py(tgt_earth)-py(tgt_top));
      ctx.strokeStyle = '#f87171'; ctx.lineWidth = 2;
      ctx.strokeRect(px(distM)-barW, py(tgt_top), barW*2, py(tgt_earth)-py(tgt_top));
    }

    // Label
    ctx.fillStyle = t.color;
    ctx.font = 'bold 9px system-ui'; ctx.textAlign = 'center';
    ctx.fillText(`T${i+1}`, px(distM), py(tgt_top) - 5);

    // Min visible annotation
    if (vis.h_min > 0) {
      ctx.fillStyle = '#f8717188';
      ctx.font = '8px system-ui'; ctx.textAlign = 'left';
      ctx.fillText(`▲${fmt(vis.h_min)}`, px(distM)+barW+3, py(tgt_min)+4);
    }
  });

  // X-axis labels: show each target distance
  ctx.fillStyle = '#64748b'; ctx.font = '9px system-ui'; ctx.textAlign = 'center';
  ctx.fillText('0', px(0), H - 4);
  const shown = new Set();
  results.forEach(r => {
    const xp = px(r.distM), label = r.distM < 1000 ? `${r.distM.toFixed(0)}m` : `${(r.distM/1000).toFixed(1)}km`;
    if ([...shown].every(sx => Math.abs(sx-xp) > 28)) {
      ctx.fillText(label, xp, H - 4);
      shown.add(xp);
    }
  });
}

// ─── Resize ───────────────────────────────────────────────────────────────────
let resizeTimer;
window.addEventListener('resize', () => { clearTimeout(resizeTimer); resizeTimer = setTimeout(compute, 100); });

// ─── Init ─────────────────────────────────────────────────────────────────────
requestAnimationFrame(() => {
  if (_saved) {
    if (_saved.k !== undefined) {
      refractionK = _saved.k;
      document.getElementById('refraction-preset').value = String(refractionK);
    }
    if (_saved.o) {
      obsElev = _saved.o[2];
      document.getElementById('obs-elev').value = obsElev;
      placeObserver(L.latLng(_saved.o[0], _saved.o[1]));
    }
    if (_saved.t) {
      _saved.t.forEach(t => addTarget(L.latLng(t[0], t[1]), t[2], t[3]));
    }
  }
  updateHint();
  compute();
});
