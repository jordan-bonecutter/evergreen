import { spawnSync } from 'node:child_process';
import { copyFileSync, cpSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const root = path.dirname(fileURLToPath(import.meta.url));
const result = spawnSync('cargo', [
  'build', '--manifest-path', path.join(root, 'compiler/Cargo.toml'),
  '--lib', '--release', '--locked', '--target', 'wasm32-unknown-unknown',
], {
  stdio: 'inherit',
  env: {
    ...process.env,
    // Browser builds use the same stack budget as the native verifier workers.
    CARGO_TARGET_WASM32_UNKNOWN_UNKNOWN_RUSTFLAGS: '-C link-arg=-zstack-size=16777216',
  },
});
if (result.error) throw result.error;
if (result.status !== 0) process.exit(result.status ?? 1);
mkdirSync(path.join(root, 'dist'), { recursive: true });
cpSync(path.join(root, 'public'), path.join(root, 'dist'), { recursive: true });
// Crop only the SVG page bounds; preserve the original drawing and its colors.
const logo = readFileSync(path.join(root, '../logo.svg'), 'utf8')
  .replace('viewBox="0 0 210 297"', 'viewBox="20 28 160 222"');
writeFileSync(path.join(root, 'dist/logo.svg'), logo);
// The favicon has its own square backdrop; page logos retain transparency.
const paths = [...logo.matchAll(/<path\b[\s\S]*?\/>/g)]
  .map(([element]) => element.replace(/\s+(?:inkscape|sodipodi):[\w-]+="[^"]*"/g, ''))
  .join('\n');
writeFileSync(path.join(root, 'dist/favicon.svg'), `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 256 256">
  <rect width="256" height="256" rx="44" fill="white"/>
  <svg x="40" y="16" width="176" height="224" viewBox="20 28 160 222">${paths}</svg>
</svg>\n`);
copyFileSync(path.join(root, 'compiler/target/wasm32-unknown-unknown/release/evergreen_browser.wasm'), path.join(root, 'dist/evergreen-compiler.wasm'));
console.log(`Built Evergreen website: ${path.join(root, 'dist')}`);
