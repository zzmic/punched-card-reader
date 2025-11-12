import os
import sys
import subprocess
from pathlib import Path

quiet = 0

# ------------------------
# Find build directory
# ------------------------
build_dir = Path("sim/bin")

if not build_dir:
    print("Error: Build directory for the project not found.")
    sys.exit(1)

if (not quiet):
    print(f"Using build directory: {build_dir}")

# ------------------------
# Determine executable path
# ------------------------
exe_name = "main"
exe_path = build_dir / exe_name

if not exe_path.is_file():
    print(f"Error: Executable {exe_path} not found.")
    sys.exit(1)

# ------------------------
# Loop over card .txt files
# ------------------------
cards_dir = Path("sim/test-cards")
card_files = sorted(cards_dir.glob("*.txt"))

if not card_files:
    print(f"No card files found in {cards_dir}")
    sys.exit(1)

for card_file in card_files:
    if (not quiet):
        print("-" * 60)
        print(f"Running {exe_path} with {card_file}")
        print("-" * 60)

    # Run the executable in the build folder so outputs go there
    result = subprocess.run(
        [str(exe_path), str(os.path.abspath(card_file))],
        cwd=str(os.getcwd()),
        input=b"done",
        stdout=sys.stdout,
        stderr=sys.stderr
    )

    if result.returncode != 0:
        print(f"Warning: {exe_path} exited with code {result.returncode}")
