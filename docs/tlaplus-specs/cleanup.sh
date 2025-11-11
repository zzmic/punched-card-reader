#!/bin/sh
# `cleanup.sh`: clean up TLA+ execution artifacts other than source files ending in `.tla` and `.cfg`.
echo 'WARNING: This script should only be executed from within the "tlaplus-specification" directory: '\
'It will recursively delete all "states" directories and all ".out", ".dvi", ".tex", and ".pdf" files in the current directory.'

# Prompt for user confirmation before proceeding.
printf "Do you want to proceed with cleanup? (y/N): "
read -r confirm
case $confirm in
    [yY])
        echo "Proceeding with cleanup..."
        ;;
    *)
        echo "Cleanup aborted."
        exit 0
        ;;
esac

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
