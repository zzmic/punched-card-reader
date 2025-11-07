CLI ?= arduino-cli
FQBN ?= arduino:renesas_uno:unor4wifi
SKETCH_DIR ?= PunchedCardReader

DEFAULT_SKETCH := $(SKETCH_DIR)/PunchedCardReader.ino

.PHONY: arduino-board-list arduino-core-update-index arduino-core-install arduino-core-list arduino-compile arduino-upload arduino-compile-punched-card-reader arduino-upload-punched-card-reader help

arduino-board-list:
	$(CLI) board list

core-update-index:
	$(CLI) core update-index

arduino-core-install:
	$(CLI) core install $(FQBN)

arduino-core-list:
	$(CLI) core list

arduino-compile:
	@[ -n "$(FILE)" ] || { echo "error: FILE variable is required (e.g., make compile FILE=$(SKETCH_DIR)/Blink.ino)" >&2; exit 1; }
	$(CLI) compile --fqbn $(FQBN) $(FILE)

arduino-upload:
	@[ -n "$(FILE)" ] || { echo "error: FILE variable is required (e.g., make upload FILE=$(SKETCH_DIR)/Blink.ino PORT=/dev/cu.usbmodemXXXX)" >&2; exit 1; }
	@[ -n "$(PORT)" ] || { echo "error: PORT variable is required (e.g., make upload FILE=$(SKETCH_DIR)/Blink.ino PORT=/dev/cu.usbmodemXXXX)" >&2; exit 1; }
	$(CLI) upload -p $(PORT) --fqbn $(FQBN) $(FILE)

arduino-compile-punched-card-reader:
	$(CLI) compile --fqbn $(FQBN) $(DEFAULT_SKETCH)

arduino-upload-punched-card-reader:
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
	@echo '  arduino-core-update-index           	Update the local cache of available platforms and libraries.'
	@echo '  arduino-core-install                	Install the core for the Arduino® UNO R4 WiFi board.'
	@echo '  arduino-core-list                   	List installed/available cores.'
	@echo '  arduino-compile                     	Compile the Arduino sketch specified in FILE.'
	@echo '  arduino-upload                      	Upload the sketch in FILE to the board on PORT.'
	@echo '  arduino-compile-punched-card-reader	Compile the default $(DEFAULT_SKETCH) sketch.'
	@echo '  arduino-upload-punched-card-reader		Upload the default $(DEFAULT_SKETCH) sketch to the board on PORT.'
	@echo '  help                        			Display this help message.'
