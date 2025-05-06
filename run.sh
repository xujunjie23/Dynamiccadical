#!/bin/bash
set -e

if [ "$#" -ne 2 ]; then
  echo "Usage: $0 <input_file.cnf> <output_dir>"
  exit 1
fi

INPUT="$1"
OUTPUT_DIR="$2"
PROOF_FILE="$OUTPUT_DIR/proof.out"

# 调用 dynamiccadical 并传递参数
./dynamiccadical "$INPUT" "$PROOF_FILE"
