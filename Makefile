CLI ?= arduino-cli
FQBN ?= arduino:renesas_uno:unor4wifi
SKETCH_DIR ?= modules/cardProcessor

CXX = /usr/bin/g++
STDFLAGS = -std=c++23
STDLIBFLAGS = -stdlib=libc++
WARNFLAGS = -Werror -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Wnull-dereference \
  -Wsign-conversion -Wimplicit-fallthrough -Wrange-loop-analysis
CXXFLAGS = $(STDFLAGS) $(STDLIBFLAGS) $(WARNFLAGS)
LDFLAGS = $(STDLIBFLAGS)
LDLIBS =
SIM_DIR = sim
SIM_CARDS_DIR = $(SIM_DIR)/test-cards
SIM_BIN_DIR = $(SIM_DIR)/bin
SIM_SOURCES = $(wildcard $(SIM_DIR)/*.cpp)
SIM_HEADERS = $(wildcard $(SIM_DIR)/*.h)
SIM_OBJECTS = $(patsubst $(SIM_DIR)/%.cpp, $(SIM_BIN_DIR)/%.o, $(SIM_SOURCES))
SIM_EXECUTABLE = $(SIM_BIN_DIR)/main
CXXFLAGS += -MMD -MP
SIM_DEPS = $(SIM_OBJECTS:.o=.d)

.PHONY: help arduino-board-list arduino-core-update-index arduino-core-install \
	arduino-core-list arduino-compile arduino-upload \
	arduino-compile-punched-card-reader arduino-upload-punched-card-reader \
	sim-build sim-format sim-clean

arduino-board-list:
	$(CLI) board list

arduino-core-update-index:
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

$(SIM_BIN_DIR):
	mkdir -p $(SIM_BIN_DIR)

$(SIM_BIN_DIR)/%.o: $(SIM_DIR)/%.cpp $(SIM_HEADERS) | $(SIM_BIN_DIR)
	$(CXX) $(CXXFLAGS) -I$(SIM_DIR) -c $< -o $@

-include $(SIM_DEPS)

$(SIM_EXECUTABLE): $(SIM_OBJECTS)
	$(CXX) $(SIM_OBJECTS) -o $@ $(LDFLAGS) $(LDLIBS)

sim-build: $(SIM_EXECUTABLE)

sim-format:
	clang-format -i sim/*.h sim/*.cpp

sim-clean:
	rm -r $(SIM_BIN_DIR)/*

sim-test: sim-clean $(SIM_EXECUTABLE)
	python3 $(SIM_DIR)/run-tests.py

sim-test-binary-mode: sim-clean $(SIM_EXECUTABLE)
	python3 $(SIM_DIR)/run-tests.py --binary-mode

help:
	@echo 'Usage: make <target> [VAR=value]'
	@echo
	@echo 'Common variables:'
	@printf '  %-30s %s\n' 'FILE' 'Path to sketch file (for compile/upload).'
	@printf '  %-30s %s\n' 'PORT' 'Serial port of the Arduino board (e.g., /dev/cu.usbmodemXXXX).'
	@echo
	@echo 'Targets:'
	@printf '  %-30s %s\n' 'arduino-core-update-index' 'Update the local cache of available platforms and libraries.'
	@printf '  %-30s %s\n' 'arduino-core-install' 'Install the core for the Arduino® UNO R4 WiFi board.'
	@printf '  %-30s %s\n' 'arduino-core-list' 'List installed/available cores.'
	@printf '  %-30s %s\n' 'arduino-compile' 'Compile the Arduino sketch specified in FILE.'
	@printf '  %-30s %s\n' 'arduino-upload' 'Upload the sketch in FILE to the board on PORT.'
	@printf '  %-30s %s\n' 'sim-build' 'Build the punched card reader simulator.'
	@printf '  %-30s %s\n' 'sim-format' 'Format the simulator source code using clang-format.'
	@printf '  %-30s %s\n' 'sim-clean' 'Clean the simulator build artifacts.'
	@printf '  %-30s %s\n' 'sim-test' 'Run the simulator tests.'
	@printf '  %-30s %s\n' 'help' 'Display this help message.'
