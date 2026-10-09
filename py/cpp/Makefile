# the the directory of this file
pwd = $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
$(info pwd = $(pwd))

LIBEXT = $(shell python3-config --extension-suffix)
$(info LIBEXT = $(LIBEXT))
default: rabin_karp$(LIBEXT)

%$(LIBEXT): %.cpp $(wildcard $(pwd)/../src/std/*.cpp) $(wildcard $(pwd)/../src/hash/*.cpp)
	$(CXX) -Wall -std=c++17 -fPIC -fdiagnostics-color -O3 $(shell python -m pybind11 --includes) $^ -shared -o $@
