CXX ?= /usr/bin/g++
STDFLAGS := -std=c++14
STDLIBFLAGS := -stdlib=libc++
WARNFLAGS := -Werror -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Wnull-dereference \
  -Wsign-conversion -Wimplicit-fallthrough -Wrange-loop-analysis
CXXFLAGS := $(STDFLAGS) $(STDLIBFLAGS) $(WARNFLAGS)
LDFLAGS := $(STDLIBFLAGS)
LDLIBS :=
SIM_DIR := .

SIM_BIN_DIR = $(SIM_DIR)/bin
SIM_SOURCES = $(wildcard $(SIM_DIR)/*.cpp)
SIM_HEADERS = $(wildcard $(SIM_DIR)/*.h)
SIM_OBJECTS = $(patsubst $(SIM_DIR)/%.cpp, $(SIM_BIN_DIR)/%.o, $(SIM_SOURCES))
SIM_EXECUTABLE = $(SIM_BIN_DIR)/main
CXXFLAGS += -MMD -MP
SIM_DEPS = $(SIM_OBJECTS:.o=.d)

.PHONY: help sim-build sim-format sim-clean sim-test sim-test-binary-mode

$(SIM_BIN_DIR):
	mkdir -p $(SIM_BIN_DIR)

$(SIM_BIN_DIR)/%.o: $(SIM_DIR)/%.cpp $(SIM_HEADERS) | $(SIM_BIN_DIR)
	$(CXX) $(CXXFLAGS) -I$(SIM_DIR) -c $< -o $@

-include $(SIM_DEPS)

$(SIM_EXECUTABLE): $(SIM_OBJECTS)
	$(CXX) $(SIM_OBJECTS) -o $@ $(LDFLAGS) $(LDLIBS)

sim-build: $(SIM_EXECUTABLE)

sim-format:
	clang-format -i *.h *.cpp

sim-clean:
	rm -rf $(SIM_BIN_DIR)/*

sim-test: sim-clean $(SIM_EXECUTABLE)
	python3 $(SIM_DIR)/run-tests.py

sim-test-binary-mode: sim-clean $(SIM_EXECUTABLE)
	python3 $(SIM_DIR)/run-tests.py --binary-mode

help:
	@echo 'Usage: make <target>'
	@echo
	@echo 'Targets:'
	@printf '  %-25s %s\n' 'sim-build' 'Build the punched card reader simulator.'
	@printf '  %-25s %s\n' 'sim-format' 'Format the simulator source code using clang-format.'
	@printf '  %-25s %s\n' 'sim-clean' 'Clean the simulator build artifacts.'
	@printf '  %-25s %s\n' 'sim-test' 'Run the simulator tests.'
	@printf '  %-25s %s\n' 'sim-test-binary-mode' 'Run the simulator tests in binary mode.'
	@printf '  %-25s %s\n' 'help' 'Display this help message.'
