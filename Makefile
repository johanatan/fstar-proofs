
.PHONY: clean all

all: createTarget primes

createTarget:
	mkdir -p target/

clean:
	rm -rf target/*

primes: primes.fst
	fstar.exe --universes --z3timeout 600 --codegen FSharp --n_cores 8 --odir target/ primes.fst

