#!/bin/sh
# Verify the whole Mizar development, in dependency order.
#
#   ./verify.sh          verify every article
#   ./verify.sh clean    remove the files Mizar generates (prel/ and text/*)
#
# Set MIZFILES to the Mizar library directory if it is not already set;
# the default below is where the Linux distribution of Mizar installs it.

set -e

cd "$(dirname "$0")"

: "${MIZFILES:=/usr/local/share/mizar}"
export MIZFILES

ARTICLES="envsyn envlen envcc envsig envbeta envpeak envnf envpar envkey \
envconf frenv_1 frenv_2 frenv_3 frenv_4 frenv_5"

if [ "$1" = "clean" ]; then
  rm -rf prel
  find text -type f ! -name '*.miz' -delete
  echo "cleaned"
  exit 0
fi

if [ ! -d "$MIZFILES/mml" ]; then
  echo "MIZFILES does not point at a Mizar library: $MIZFILES" >&2
  echo "Set MIZFILES to the directory containing mml/ and prel/." >&2
  exit 1
fi

if ! command -v mizf > /dev/null 2>&1; then
  echo "mizf was not found on PATH. Install Mizar and add its bin/ to PATH." >&2
  exit 1
fi

fail() {
  echo "FAILED"
  echo "--- text/$1.err (line column error-code) ---"
  cat "text/$1.err"
  echo
  echo 'Verification FAILED. Look error codes up in $MIZFILES/mizar.msg.'
  exit 1
}

mkdir -p prel

for a in $ARTICLES; do
  printf '%-10s ' "$a"
  mizf "text/$a.miz" > /dev/null 2>&1 || true
  if [ -s "text/$a.err" ]; then fail "$a"; fi
  miz2prel "text/$a.miz" > /dev/null 2>&1
  echo "ok"
done

# The audit article restates each main result and justifies it by its
# citation alone. It is a leaf: nothing imports it, so it is not exported.
printf '%-10s ' audit
mizf text/audit.miz > /dev/null 2>&1 || true
if [ -s text/audit.err ]; then fail audit; fi
echo "ok"

echo
echo "All 15 articles verified with no errors, and the audit article"
echo "re-derives each main result from its citation alone."
echo "Main theorem: FRENV_5:8  (FrRed(V) is confluent)"
