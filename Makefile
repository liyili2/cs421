OCAMLC=ocamlc
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc
GMAKE=make
RM=rm
CP=cp
LN=ln
MV=mv
TAR=tar
GZIP=gzip
MKDIR=mkdir


parser.cmo: k.cmo
	$(OCAMLYACC) parser.mly
<<<<<<< HEAD
        $(OCAMLC) -c parser.mli
=======
	$(OCAMLC) -c parser.mli
>>>>>>> 0d850fea7d4b3d596c58997c6e3bee76651d4efd
	$(OCAMLC) -c parser.ml


lexer.cmo: parser.cmo
	$(OCAMLLEX) lexer.mll
	$(OCAMLC) -c lexer.ml

k.cmo: k.ml
	$(OCAMLC) -c k.ml


clean:
	rm -fr *.cm? lexer.ml parser.ml parser.mli
