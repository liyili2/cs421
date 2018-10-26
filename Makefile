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
	$(OCAMLC) -c parser.mli
	$(OCAMLC) -c parser.ml


lexer.cmo: parser.cmo
	$(OCAMLLEX) lexer.mll
	$(OCAMLC) -c lexer.ml

cpsLexer.cmo: cpsParser.cmo
	$(OCAMLLEX) cpsLexer.mll
	$(OCAMLC) -c cpsLexer.ml

cpsParser.cmo: k.cmo
	$(OCAMLYACC) cpsParser.mly
	$(OCAMLC) -c cpsParser.mli
	$(OCAMLC) -c cpsParser.ml

k.cmo: k.ml
	$(OCAMLC) -c k.ml




clean:
	rm -fr *.cm? lexer.ml parser.ml parser.mli
