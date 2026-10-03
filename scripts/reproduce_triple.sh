#!/usr/bin/env bash
set -eu
script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
exec python3 -B "$script_dir/reproduce_triple.py" "$@"
