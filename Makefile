build:
	cabal new-build readme
	cabal new-test readme

repl:
	cabal new-repl readme

.PHONY: build repl
