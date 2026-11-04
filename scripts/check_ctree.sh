#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
export ATTENTION_ROOT="$root"
if [ ! -x .venv-attention/bin/python ]; then
  echo 'Run ATTENTION_PYTHON=python3.12 sh scripts/bootstrap_attention.sh first.' >&2
  exit 1
fi
dune build @all
dune runtest
for stage in hfusion hivm; do
  dune exec kernel-example -- --backend ctree --stage "$stage" \
    --ir "artifacts/kernel_IR/vector-add/$stage.mlir" --length 777 \
    --output "_build/ctree-$stage.json"
done
