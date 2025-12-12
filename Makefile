CLI ?= arduino-cli
FQBN ?= arduino:renesas_uno:unor4wifi
SKETCH_DIR ?= arduino/punchedCardReader

.PHONY: help arduino-board-list arduino-core-update-index arduino-core-install \
	arduino-core-list arduino-compile arduino-compile-and-upload

arduino-board-list:
	$(CLI) board list

arduino-core-update-index:
	$(CLI) core update-index

arduino-core-install:
	$(CLI) core install $(FQBN)

arduino-core-list:
	$(CLI) core list

arduino-compile:
	@[ -n "$(FILE)" ] || { echo "error: FILE variable is required (e.g., make compile FILE=$(SKETCH_DIR)/punchedCardReader.ino)" >&2; exit 1; }
	$(CLI) compile --fqbn $(FQBN) --export-binaries $(FILE)

arduino-compile-and-upload:
	@[ -n "$(FILE)" ] || { echo "error: FILE variable is required (e.g., make upload PORT=/dev/cu.usbmodemXXXX) FILE=$(SKETCH_DIR)/punchedCardReader.ino" >&2; exit 1; }
	@[ -n "$(PORT)" ] || { echo "error: PORT variable is required (e.g., make upload PORT=/dev/cu.usbmodemXXXX) FILE=$(SKETCH_DIR)/punchedCardReader.ino" >&2; exit 1; }
	$(CLI) compile --fqbn $(FQBN) --export-binaries $(FILE)
	$(CLI) upload -p $(PORT) --fqbn $(FQBN) $(FILE)

help:
	@echo 'Usage: make <target> [VAR=value]'
	@echo
	@echo 'Common variables:'
	@printf '  %-30s %s\n' 'FILE' 'Path to sketch file (for compile/upload).'
	@printf '  %-30s %s\n' 'PORT' 'Serial port of the Arduino board (e.g., /dev/cu.usbmodemXXXX).'
	@echo
	@echo 'Targets:'
	@printf '  %-30s %s\n' 'arduino-board-list' 'List connected Arduino boards.'
	@printf '  %-30s %s\n' 'arduino-core-update-index' 'Update the local cache of available platforms and libraries.'
	@printf '  %-30s %s\n' 'arduino-core-install' 'Install the core for the Arduino® UNO R4 WiFi board.'
	@printf '  %-30s %s\n' 'arduino-core-list' 'List installed/available cores.'
	@printf '  %-30s %s\n' 'arduino-compile' 'Compile the Arduino sketch specified in FILE.'
	@printf '  %-30s %s\n' 'arduino-compile-and-upload' 'Compile and upload the Arduino sketch specified in FILE to the board at PORT.'
	@printf '  %-30s %s\n' 'help' 'Display this help message.'
