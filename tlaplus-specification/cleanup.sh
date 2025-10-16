#!/bin/sh
# `cleanup.sh`: clean up TLA+ execution artifacts other than source files ending in `.tla` and `.cfg`.
echo 'WARNING: This script should only be executed from within the "tlaplus-specification" directory.'
echo '         It will recursively delete all "states" directories and all ".out", ".dvi", ".tex", and ".pdf" files in the current directory.'

# Remove all `states` directories in the current directory recursively.
find . -type d -name states -prune -exec rm -r {} +

# Remove all `.out` files in the current directory recursively.
find . -type f -name "*.out" -delete

# Remove all `.dvi` files in the current directory recursively.
find . -type f -name "*.dvi" -delete

# Remove all `.tex` files in the current directory recursively.
find . -type f -name "*.tex" -delete

# Remove all `.pdf` files in the current directory recursively.
find . -type f -name "*.pdf" -delete

echo "Cleanup (of TLA+ execution artifacts) complete."
