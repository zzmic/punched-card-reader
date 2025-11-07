CLI ?= arduino-cli
FQBN ?= arduino:renesas_uno:unor4wifi
SKETCH_DIR ?= PunchedCardReader

DEFAULT_SKETCH := $(SKETCH_DIR)/PunchedCardReader.ino

.PHONY: board-list core-update-index core-install core-list compile upload compile-punched-card-reader upload-punched-card-reader help

board-list:
	$(CLI) board list

core-update-index:
	$(CLI) core update-index

core-install:
	$(CLI) core install $(FQBN)

core-list:
	$(CLI) core list

compile:
	@[ -n "$(FILE)" ] || { echo "error: FILE variable is required (e.g., make compile FILE=$(SKETCH_DIR)/Blink.ino)" >&2; exit 1; }
	$(CLI) compile --fqbn $(FQBN) $(FILE)

upload:
	@[ -n "$(FILE)" ] || { echo "error: FILE variable is required (e.g., make upload FILE=$(SKETCH_DIR)/Blink.ino PORT=/dev/cu.usbmodemXXXX)" >&2; exit 1; }
	@[ -n "$(PORT)" ] || { echo "error: PORT variable is required (e.g., make upload FILE=$(SKETCH_DIR)/Blink.ino PORT=/dev/cu.usbmodemXXXX)" >&2; exit 1; }
	$(CLI) upload -p $(PORT) --fqbn $(FQBN) $(FILE)

compile-punched-card-reader:
	$(CLI) compile --fqbn $(FQBN) $(DEFAULT_SKETCH)

upload-punched-card-reader:
	@[ -n "$(PORT)" ] || { echo "error: PORT variable is required (e.g., make upload-punched-card-reader PORT=/dev/cu.usbmodemXXXX)" >&2; exit 1; }
	$(CLI) upload -p $(PORT) --fqbn $(FQBN) $(DEFAULT_SKETCH)

help:
	@echo 'Usage: make <target> [VAR=value]'
	@echo
	@echo 'Common variables:'
	@echo '  FILE   Path to sketch file (for compile/upload).'
	@echo '  PORT   Serial port of the Arduino board (e.g., /dev/cu.usbmodemXXXX).'
	@echo
	@echo 'Targets:'
	@echo '  core-update-index           	Update the local cache of available platforms and libraries.'
	@echo '  core-install                	Install the core for the Arduino® UNO R4 WiFi board.'
	@echo '  core-list                   	List installed/available cores.'
	@echo '  compile                     	Compile the Arduino sketch specified in FILE.'
	@echo '  upload                      	Upload the sketch in FILE to the board on PORT.'
	@echo '  compile-punching-card-reader	Compile the default $(DEFAULT_SKETCH) sketch.'
	@echo '  upload-punching-card-reader	Upload the default $(DEFAULT_SKETCH) sketch to the board on PORT.'
	@echo '  help                        	Display this help message.'
