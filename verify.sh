#!/usr/bin/env bash
# 一鍵驗證：跑完所有檢查、測試、編譯期證明，並輸出零開銷證據。
set -euo pipefail
export PATH="$HOME/.moon/bin:$PATH"
cd "$(dirname "$0")"

echo "===== 1. 全部套件檢查（真計算） ====="
moon run run

echo
echo "===== 2. 單元 + 整合測試 ====="
moon test

echo
echo "===== 3. 編譯期 SMT 證明（moon prove） ====="
moon prove

echo
echo "===== 4. 零開銷：單態化證據 ====="
moon build run --target wasm --output-wat >/dev/null
WAT=_build/wasm/debug/build/run/run.wat
echo "horner 的單態實例："
grep -oE 'horner[A-Za-z0-9]*' "$WAT" | sort -u
echo "直接呼叫 call：      $(grep -oE '\bcall \$' "$WAT" | wc -l)"
echo "間接呼叫 call_indirect：$(grep -c 'call_indirect' "$WAT")"
