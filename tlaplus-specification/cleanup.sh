#!/bin/sh
# `cleanup.sh`: clean up TLA+ execution artifacts.

# Remove all `states` directories recursively.
find . -type d -name states -prune -exec rm -rf {} +

# Remove all `.out` files recursively.
find . -type f -name "*.out" -delete

echo "Cleanup (of TLA+ execution artifacts) complete."
