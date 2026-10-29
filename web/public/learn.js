import { lessons, meetsGoal } from './lessons.js';
import { mountPlayground } from './playground.js';

const $ = id => document.getElementById(id);
const storageKey = 'evergreen.learn.v1';
const drafts = {};
const completed = {};
let index = 0;
let hintCount = 0;
let playground;
try {
  const saved = JSON.parse(localStorage.getItem(storageKey));
  for (const lesson of lessons) {
    if ((saved?.revisions?.[lesson.id] ?? 1) !== (lesson.revision ?? 1)) continue;
    const draft = saved?.drafts?.[lesson.id];
    if (typeof draft === 'string' && draft.length <= 100_000) drafts[lesson.id] = draft;
    if (saved?.completed?.[lesson.id] === drafts[lesson.id]) completed[lesson.id] = drafts[lesson.id];
  }
  const savedIndex = lessons.findIndex(lesson => lesson.id === saved?.lesson);
  if (savedIndex >= 0) index = savedIndex;
} catch { /* Start fresh when storage is disabled, missing, or corrupt. */ }

function save() {
  try { localStorage.setItem(storageKey, JSON.stringify({ drafts, completed, lesson: lessons[index].id, revisions: Object.fromEntries(lessons.map(lesson => [lesson.id, lesson.revision ?? 1])) })); } catch { /* Lessons work without storage. */ }
}
function draft(lesson) { return drafts[lesson.id] ?? lesson.starter; }
function isComplete(lesson) { return typeof completed[lesson.id] === 'string' && completed[lesson.id] === draft(lesson); }
function updateOutline() {
  for (const [i, link] of [...$('lesson-list').children].entries()) {
    const done = isComplete(lessons[i]);
    if (i === index) link.setAttribute('aria-current', 'step');
    else link.removeAttribute('aria-current');
    link.classList.toggle('is-complete', done);
    link.firstChild.textContent = done ? '✓' : String(i + 1).padStart(2, '0');
    link.setAttribute('aria-label', `${i + 1}. ${lessons[i].title}${done ? ', completed' : ''}`);
  }
}
function feedback(message, className = '') {
  $('goal-feedback').textContent = message;
  $('goal-feedback').className = `goal-feedback ${className}`;
}
// Render inline code without treating lesson prose as HTML.
function renderInline(element, text) {
  const fragments = text.split(/(`[^`]+`)/g).map(part => {
    if (!part.startsWith('`')) return document.createTextNode(part);
    const code = document.createElement('code');
    code.textContent = part.slice(1, -1);
    return code;
  });
  element.replaceChildren(...fragments);
}
function renderWalkthrough(lesson) {
  $('proof-walkthrough').hidden = !lesson.walkthrough;
  $('proof-walkthrough').open = !!lesson.walkthrough;
  $('proof-steps').replaceChildren();
  for (const step of lesson.walkthrough ?? []) {
    const item = document.createElement('li');
    const title = document.createElement('h3');
    title.textContent = step.title;
    const body = document.createElement('p');
    renderInline(body, step.text);
    const goals = document.createElement('pre');
    goals.textContent = step.goals;
    item.append(title, body, goals);
    $('proof-steps').append(item);
  }
}
function renderLesson(focus = false) {
  const lesson = lessons[index];
  hintCount = 0;
  $('lesson-title').textContent = lesson.title;
  renderInline($('lesson-introduction'), lesson.introduction);
  renderWalkthrough(lesson);
  renderInline($('goal'), lesson.goal);
  $('expected').textContent = lesson.expected.output ? `Output: ${lesson.expected.output.trimEnd()}` : `main → ${lesson.expected.result}`;
  $('hints').replaceChildren();
  $('hints').hidden = true;
  $('hint').disabled = false;
  $('hint').textContent = 'Need a hint?';
  $('hint').setAttribute('aria-expanded', 'false');
  $('hint-count').textContent = '';
  $('proof-explanation').hidden = !lesson.why;
  $('proof-why').textContent = lesson.why ?? '';
  $('takeaway').hidden = !isComplete(lesson);
  renderInline($('takeaway-text'), lesson.takeaway);
  $('previous').disabled = index === 0;
  $('next').hidden = index === lessons.length - 1;
  $('open-playground').hidden = index !== lessons.length - 1;
  document.title = `${lesson.title} — Learn Evergreen`;
  feedback(isComplete(lesson) ? '✓ Goal complete. Try another approach or continue to the next example.' : 'Make your change, then run to check your goal.', isComplete(lesson) ? 'is-complete' : '');
  updateOutline();
  if (focus) $('lesson-title').focus({ preventScroll: false });
}
function navigate() {
  const id = location.hash.slice(1);
  const next = lessons.findIndex(lesson => lesson.id === id);
  if (next < 0 || next === index) return;
  index = next;
  playground.setSource(draft(lessons[index]));
  renderLesson(true);
  save();
}
function goTo(next) { location.hash = lessons[next].id; }

for (const [i, lesson] of lessons.entries()) {
  const link = document.createElement('a');
  link.href = `#${lesson.id}`;
  link.className = 'lesson-link';
  const number = document.createElement('span');
  number.className = 'lesson-number';
  number.setAttribute('aria-hidden', 'true');
  const title = document.createElement('span');
  title.textContent = lesson.title;
  link.append(number, title);
  $('lesson-list').append(link);
}
const hashIndex = lessons.findIndex(lesson => lesson.id === location.hash.slice(1));
if (hashIndex >= 0) index = hashIndex;
history.replaceState(null, '', `#${lessons[index].id}`);
renderLesson();
playground = mountPlayground({
  initialSource: draft(lessons[index]),
  onEdit(source) {
    drafts[lessons[index].id] = source;
    $('takeaway').hidden = true;
    feedback('Code changed. Run again to check your goal.');
    updateOutline(); save();
  },
  onRunningChange(running) {
    $('complete').disabled = running;
    if (running) feedback('Checking your code with the Evergreen compiler…');
  },
  onResult(data, snapshot) {
    if ($('source').value !== snapshot) {
      feedback('That run used an earlier draft. Run your current code to check the goal.');
      return;
    }
    const lesson = lessons[index];
    if (meetsGoal(lesson, data)) {
      drafts[lesson.id] = snapshot;
      completed[lesson.id] = snapshot;
      $('takeaway').hidden = false;
      feedback(index === lessons.length - 1 ? '✓ Proof checked. You’ve completed the short course!' : '✓ Goal complete. Read what you learned, then try the next example.', 'is-complete');
      updateOutline(); save();
    } else if (!data.ok) {
      feedback('The compiler found an issue. Use the diagnostic above, or reveal a hint.', 'needs-work');
    } else if (data.runtimeError) {
      feedback('Execution stopped. Check the output above and try again.', 'needs-work');
    } else {
      feedback(`Your code compiled, but the goal is not complete. Expected ${lesson.expected.output ? JSON.stringify(lesson.expected.output) : `main → ${lesson.expected.result}`}. Keep the lesson’s contract and structure as you work.`, 'needs-work');
    }
  },
});
$('hint').addEventListener('click', () => {
  const lesson = lessons[index];
  if (hintCount >= lesson.hints.length) return;
  const item = document.createElement('li');
  renderInline(item, lesson.hints[hintCount++]);
  $('hints').append(item);
  $('hints').hidden = false;
  $('hint').setAttribute('aria-expanded', 'true');
  $('hint-count').textContent = `${hintCount} / ${lesson.hints.length}`;
  $('hint').textContent = hintCount === lesson.hints.length ? 'All hints revealed' : 'Another hint';
  $('hint').disabled = hintCount === lesson.hints.length;
});
$('complete').addEventListener('click', () => {
  const lesson = lessons[index];
  drafts[lesson.id] = lesson.solution;
  playground.setSource(lesson.solution);
  feedback('Solution filled in. Run code to check it and see the output.');
  updateOutline(); save();
  playground.run();
});
$('reset').addEventListener('click', () => {
  const lesson = lessons[index];
  drafts[lesson.id] = lesson.starter;
  delete completed[lesson.id];
  playground.setSource(lesson.starter);
  renderLesson(); save();
});
$('previous').addEventListener('click', () => { if (index > 0) goTo(index - 1); });
$('next').addEventListener('click', () => { if (index < lessons.length - 1) goTo(index + 1); });
window.addEventListener('hashchange', navigate);
