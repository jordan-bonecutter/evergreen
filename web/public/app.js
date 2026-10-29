import { examples } from './examples.js';
import { mountPlayground } from './playground.js';

const picker = document.getElementById('example');
const storageKey = 'evergreen.playground.v2';
let initialSource = examples.hello;
try {
  const saved = JSON.parse(localStorage.getItem(storageKey));
  if (saved && typeof saved.source === 'string' && saved.source.length <= 100_000) {
    initialSource = saved.source;
    if (Object.hasOwn(examples, saved.example)) picker.value = saved.example;
  }
} catch { /* Storage may be disabled or corrupt. */ }
function save(source) {
  try { localStorage.setItem(storageKey, JSON.stringify({source, example: picker.value})); } catch { /* Storage may be disabled. */ }
}
const playground = mountPlayground({initialSource, onEdit: save});
picker.addEventListener('change', () => {
  playground.setSource(examples[picker.value]);
  save(examples[picker.value]);
});
document.getElementById('reset').addEventListener('click', () => {
  playground.setSource(examples[picker.value]);
  save(examples[picker.value]);
});
