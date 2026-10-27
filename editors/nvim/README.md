# Evergreen for Neovim

Provides `.evg` filetype detection, syntax highlighting (including contracts and
proof tactics), four-space indentation using Neovim's C indent engine, and `//`
comment settings. No plugin manager or parser download is required. This is
runtime support; it does not provide an LSP server or compiler completion.

From the repository root, run:

```sh
./scripts/install-nvim.sh
```

The script copies the runtime files into
`${XDG_DATA_HOME:-$HOME/.local/share}/${NVIM_APPNAME:-nvim}/site/pack/evergreen/start/evergreen`.
It can be run from any working directory and rerun to update the installed files.
Restart Neovim after installing. Filetype plugins and syntax highlighting must be
enabled (Neovim enables both by default).

For a custom Neovim data directory:

```sh
./scripts/install-nvim.sh /path/to/nvim-data
```

For a plugin manager, use `editors/nvim` as the plugin's runtime directory.
Indentation is a brace-based heuristic; use `gg=G` to reindent a buffer. Buffer
settings can be overridden in your `after/ftplugin/evergreen.vim`.

To uninstall, remove only the `site/pack/evergreen/start/evergreen` directory
inside the data directory used at installation. The installer copies files, so
moving or deleting this checkout does not break the installed support.
