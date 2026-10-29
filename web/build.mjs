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
copyFileSync(path.join(root, 'compiler/target/wasm32-unknown-unknown/release/evergreen_browser.wasm'), path.join(root, 'dist/evergreen-compiler.wasm'));
console.log(`Built Evergreen website: ${path.join(root, 'dist')}`);
