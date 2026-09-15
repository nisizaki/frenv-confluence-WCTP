#!/bin/sh
# Verify one article and print its error file.
#
#   ./check.sh enveps_1
#
# The articles depend on each other, so the ones before it in the order used
# by verify.sh must already have been exported to prel/.

set -e

cd "$(dirname "$0")"

: "${MIZFILES:=/usr/local/share/mizar}"
export MIZFILES

if [ -z "$1" ]; then
  echo "usage: ./check.sh <article-name-without-extension>" >&2
  exit 1
fi

mizf "text/$1.miz" || true
echo "=== text/$1.err (line column error-code) ==="
cat "text/$1.err"
echo "=== end ==="
