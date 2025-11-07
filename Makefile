CLI ?= arduino-cli
FQBN ?= arduino:renesas_uno
PORT ?= /dev/ttyACM0
SKETCH_DIR ?= PunchedCardReader

DEFAULT_SKETCH := $(SKETCH_DIR)/PunchedCardReader.ino

.PHONY: core-update core-install core-list compile upload compile-punching-card-reader upload-punching-card-reader help

core-update:
	$(CLI) core update-index

core-install:
	$(CLI) core install $(FQBN)

core-list:
	$(CLI) core list

compile:
	@[ -n "$(FILE)" ] || { echo "error: FILE variable is required (e.g. make compile FILE=$(SKETCH_DIR)/Blink.ino)" >&2; exit 1; }
	$(CLI) compile --fqbn $(FQBN) $(FILE)

upload:
	@[ -n "$(FILE)" ] || { echo "error: FILE variable is required (e.g. make upload FILE=$(SKETCH_DIR)/Blink.ino)" >&2; exit 1; }
	$(CLI) upload -p $(PORT) --fqbn $(FQBN) $(FILE)

compile-punching-card-reader:
	$(CLI) compile --fqbn $(FQBN) $(DEFAULT_SKETCH)

upload-punching-card-reader:
	$(CLI) upload -p $(PORT) --fqbn $(FQBN) $(DEFAULT_SKETCH)

help:
	@echo 'Usage: make <target>'
	@echo 'Targets:'
	@echo '  core-update: Update the local cache of available platforms and libraries.'
	@echo '  core-install: Install the core for the Arduino® UNO R4 WiFi board.'
	@echo '  core-list: List installed/available cores.'
	@echo '  compile: Compile the Arduino sketch specified in the `FILE` variable.'
	@echo '  upload: Upload the compiled sketch specified in the `FILE` variable to the connected Arduino® UNO R4 WiFi board.'
	@echo '  compile-punching-card-reader: Compile the default `PunchedCardReader/PunchedCardReader.ino` sketch.'
	@echo '  upload-punching-card-reader: Upload the compiled (default) `PunchedCardReader/PunchedCardReader.ino` sketch to the connected Arduino® UNO R4 WiFi board.'
	@echo '  help: Display this help message.'
