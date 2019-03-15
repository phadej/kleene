build :
	cabal new-build

doctest :
	mv .ghc.environment.x86_64-linux-8.4.4 tmp
	grep -v base-compat-0 tmp > .ghc.environment.x86_64-linux-8.4.4
	rm tmp
	doctest --fast src/

haddock :
	cabal new-haddock --haddock-hyperlink-source

ghcid :
	ghcid -c 'cabal new-repl'
