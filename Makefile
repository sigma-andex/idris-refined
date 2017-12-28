.DEFAULT_GOAL := build

all: install

install: build
	idris --install idris-refined.ipkg

build:
	idris --build idris-refined.ipkg

test: build
	idris --testpkg idris-refined-test.ipkg

clean:
	idris --clean idris-refined.ipkg
