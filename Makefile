build :
	cabal new-build

doctest :
	perl -i -e 'while (<ARGV>) { print unless /package-id\s+(base-compat)-\d+(\.\d+)*/; }' .ghc.environment.*
	doctest --fast src/

haddock :
	cabal new-haddock --haddock-hyperlink-source

ghcid :
	ghcid -c 'cabal new-repl'
