import { cpSync, rmSync, mkdirSync } from 'fs';

const files = ['index.html', 'app.css', 'app.js', 'view3d.js'];

rmSync('dist', { recursive: true, force: true });
mkdirSync('dist');
files.forEach(f => cpSync(f, `dist/${f}`));
console.log(`Built ${files.length} files → dist/`);
