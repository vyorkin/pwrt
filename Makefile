build:
	cabal new-build
	cabal new-test

repl:
	cabal new-repl readme

.PHONY: build repl
