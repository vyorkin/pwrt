PANDOC=cabal new-exec -- pandoc
LHS := $(sort $(wildcard src/*.lhs))

build:
	cabal new-build

readme: build
	mkdir -p dist
	cat $(LHS) > dist/all.lhs
	$(PANDOC) --from=markdown+lhs --to=markdown dist/all.lhs -o dist/all.md
	cat INTRO.md dist/all.md > README.md

repl:
	cabal new-repl

clean:
	cabal new-clean

.PHONY: build repl clean readme
