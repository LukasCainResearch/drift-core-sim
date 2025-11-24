# DRIFT SYSTEMS INC.
# Standard Build System for Drift Core Simulation

CXX = g++
CXXFLAGS = -O3 -std=c++17 -Wall

all: drift_gen

drift_gen: dad_tool.cpp dad_config.h
	$(CXX) $(CXXFLAGS) dad_tool.cpp -o drift_gen

clean:
	rm -f drift_gen *.bin *.o

test: drift_gen
	./drift_gen 1000000 > test_stream.bin
	@echo "Generated 1MB test stream."
