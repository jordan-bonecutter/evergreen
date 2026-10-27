#!/bin/sh
# Install a self-contained native Neovim package; no init.lua changes needed.
set -eu

usage() {
    echo "Usage: $0 [NVIM_DATA_DIRECTORY]"
    echo "Default: \${XDG_DATA_HOME:-\$HOME/.local/share}/\${NVIM_APPNAME:-nvim}"
}
case ${1-} in
    -h|--help) usage; exit 0 ;;
esac
if [ "$#" -gt 1 ]; then
    usage >&2
    exit 1
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
source_dir=$script_dir/../editors/nvim
data_dir=${1:-${XDG_DATA_HOME:-$HOME/.local/share}/${NVIM_APPNAME:-nvim}}
if [ -z "$data_dir" ]; then
    echo 'Neovim data directory must not be empty.' >&2
    exit 1
fi
package_dir=$data_dir/site/pack/evergreen/start/evergreen
for directory in ftdetect ftplugin syntax; do
    mkdir -p "$package_dir/$directory"
    cp "$source_dir/$directory/evergreen.vim" "$package_dir/$directory/evergreen.vim"
done
printf 'Installed Evergreen Neovim support to %s\nRestart Neovim to load it.\n' "$package_dir"
