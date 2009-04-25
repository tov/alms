EXE     = affine
GHC     = ghc

default: Setup dist/setup-config
	./Setup build
	cp dist/build/affine/affine .

dist/setup-config config: Setup affine.cabal
	./Setup configure

Setup: Setup.hs
	$(GHC) -o $@ --make $<

$(EXE): default


examples: $(EXE)
	for i in examples/ex*.aff; do \
	  echo "$$i"; \
	  head -1 $$i; \
	  ./$(EXE) $$i; \
	  echo; \
	done

clean:
	$(RM) *.hi *.o $(EXE) $(TARBALL) Setup
	$(RM) -Rf $(DISTDIR) dist


VERSION = 0.3.2
DISTDIR = affine-contracts-$(VERSION)
TARBALL = $(DISTDIR).tar.gz

dist: $(TARBALL)

$(TARBALL):
	$(RM) -Rf $(TARBALL) $(DISTDIR)
	svn export . $(DISTDIR)
	tar czf $(TARBALL) $(DISTDIR)
	$(RM) -Rf $(DISTDIR)
	chmod a+r $(TARBALL)
