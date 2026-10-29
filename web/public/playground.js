export function mountPlayground({ initialSource, onEdit = () => {}, onResult = () => {}, onRunningChange = () => {} }) {
  const $ = id => document.getElementById(id);
  const source = $('source');
  const run = $('run');
  const runLabel = $('run-label');
  const status = $('status');
  const output = $('output');
  const result = $('execution-result');
  const stop = $('stop');
  const download = $('download');
  let worker;
  let ready = false;
  let running = false;
  let timeout;
  let snapshot = '';
  let downloadUrl;
  let failedLoad = false;

  function countLines() {
    $('line-numbers').textContent = Array.from({ length: source.value.split('\n').length }, (_, i) => i + 1).join('\n');
    $('line-numbers').scrollTop = source.scrollTop;
  }

  function clearDownload() {
    if (downloadUrl) URL.revokeObjectURL(downloadUrl);
    downloadUrl = undefined;
    download.hidden = true;
  }

  function clearConsole() {
    output.className = '';
    output.textContent = 'Ready when you are.\n\nRun the example to see its output here.';
    result.hidden = true;
    result.textContent = '';
    $('trust').hidden = true;
    $('trust').open = false;
    clearDownload();
  }

  function setRunning(value) {
    running = value;
    run.disabled = value || !ready;
    runLabel.textContent = value ? 'Running…' : ready ? 'Run code' : 'Loading compiler…';
    stop.hidden = !value;
    $('reset').disabled = value;
    $('clear').disabled = value;
    onRunningChange(value);
  }

  function finish(message) {
    clearTimeout(timeout);
    setRunning(false);
    status.textContent = message;
  }

  function display(data) {
    output.className = 'has-output';
    if (!data.ok) {
      output.classList.add('is-error');
      output.textContent = `${data.stage === 'verify' ? 'Verification failed' : data.stage === 'compile' ? 'Wasm compilation failed' : 'Compiler error'}\n\n${data.error}`;
      finish('Could not run · see compiler diagnostic');
      onResult(data, snapshot);
      return;
    }
    output.textContent = data.output || '(No console output.)';
    result.hidden = false;
    result.textContent = data.runtimeError || `main → ${data.result}`;
    if (data.runtimeError) output.classList.add('is-error');
    const assumptions = data.assumptions ?? [];
    if (assumptions.length) {
      $('trust').hidden = false;
      $('trust-summary').textContent = `${assumptions.length} trusted assumption${assumptions.length === 1 ? '' : 's'} · inspect the boundary`;
      $('trust-details').textContent = assumptions.map(a => `Line ${a.line}: ${a.goal}`).join('\n');
    }
    if (data.module && source.value === snapshot) {
      downloadUrl = URL.createObjectURL(new Blob([data.module], { type: 'application/wasm' }));
      download.hidden = false;
    }
    onResult(data, snapshot);
    const checked = assumptions.length ? `Checked · ${assumptions.length} trusted assumption${assumptions.length === 1 ? '' : 's'}` : 'Verified';
    finish(`${data.runtimeError ? 'Execution stopped' : checked} · ${data.obligations} obligations · ${data.elapsed} ms${source.value !== snapshot ? ' · source edited since this run' : ''}`);
  }

  function startWorker() {
    worker?.terminate();
    ready = false;
    failedLoad = false;
    run.disabled = true;
    runLabel.textContent = 'Loading compiler…';
    try {
      worker = new Worker(new URL('./worker.js', import.meta.url), { type: 'module' });
      worker.onmessage = ({ data }) => {
        if (data.type === 'ready') {
          ready = true;
          run.disabled = false;
          runLabel.textContent = 'Run code';
          if (!running) status.textContent = 'Compiler ready · runs locally in WebAssembly';
        } else if (data.type === 'phase' && running) status.textContent = data.message;
        else if (data.type === 'result' && running) display(data);
        else if (data.type === 'load-error') loadError(data.error);
      };
      worker.onerror = event => {
        if (running) {
          output.className = 'is-error';
          output.textContent = `Compiler worker stopped: ${event.message || 'an unexpected error occurred.'}`;
          finish('Compiler worker stopped · restarting');
          startWorker();
        } else loadError(event.message || 'The browser could not load the compiler worker.');
      };
    } catch (error) { loadError(error.message); }
  }

  function loadError(message) {
    failedLoad = true;
    ready = false;
    clearTimeout(timeout);
    setRunning(false);
    run.disabled = false;
    runLabel.textContent = 'Retry loading';
    status.textContent = 'Compiler unavailable · retry to load';
    output.className = 'is-error';
    output.textContent = `${message}\n\nServe the built site over HTTP and use a browser with WebAssembly and module Worker support.`;
  }

  function runCode() {
    if (failedLoad) { startWorker(); return; }
    if (!ready || running) return;
    clearConsole();
    snapshot = source.value;
    setRunning(true);
    status.textContent = 'Checking proofs and compiling to Wasm…';
    output.textContent = 'Working…';
    worker.postMessage({ type: 'run', source: snapshot });
    timeout = setTimeout(() => cancel('Stopped after 20 seconds. Try a smaller program.'), 20_000);
  }

  function cancel(message = 'Execution stopped.') {
    clearTimeout(timeout);
    worker?.terminate();
    output.className = '';
    output.textContent = message;
    setRunning(false);
    startWorker();
    status.textContent = message;
  }

  source.value = initialSource;
  countLines();

  source.addEventListener('input', () => {
    countLines(); onEdit(source.value); clearDownload();
    if (ready && !running) status.textContent = 'Source edited · run to update output';
  });
  source.addEventListener('scroll', () => { $('line-numbers').scrollTop = source.scrollTop; });
  source.addEventListener('keydown', event => {
    // Tab indents in the editor; Shift+Tab keeps keyboard navigation available.
    if (event.key === 'Tab' && !event.shiftKey && !event.altKey && !event.ctrlKey && !event.metaKey) {
      event.preventDefault();
      source.setRangeText('    ', source.selectionStart, source.selectionEnd, 'end');
      source.dispatchEvent(new Event('input'));
    }
  });
  document.addEventListener('keydown', event => {
    if (event.key === 'Enter' && (event.ctrlKey || event.metaKey)) { event.preventDefault(); runCode(); }
  });
  $('clear').addEventListener('click', clearConsole);
  run.addEventListener('click', runCode);
  stop.addEventListener('click', () => cancel());
  download.addEventListener('click', () => {
    if (!downloadUrl) return;
    const link = document.createElement('a');
    link.href = downloadUrl; link.download = 'main.wasm'; link.click();
  });
  window.addEventListener('pagehide', () => { clearTimeout(timeout); worker?.terminate(); clearDownload(); });
  window.addEventListener('pageshow', event => { if (event.persisted) { setRunning(false); startWorker(); } });
  startWorker();

  return {
    run: runCode,
    setSource(value) {
      if (running) cancel();
      source.value = value;
      countLines(); clearConsole();
      if (ready) status.textContent = 'Ready to run · code stays in your browser';
    },
  };
}
