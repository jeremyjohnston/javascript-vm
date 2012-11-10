############################################################################
# You can define your own path to COQBIN by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#    COQBIN=/var/tmp/charguer/v8.4/bin/
#
# The same applies for the path to tlc, e.g.: TLC=~/tlc/trunk
#
# Note that TLC should have no leading slash, whereas COQBIN should have one.
# Note that if you rebind COQBIN you need to do the same in the TLC folder.
# Note that if you add a settings.sh file, you need to do "make clean" first.

# Default paths for TLC and COQBIN are as follows:

TLC=tlc
FLOCQ=flocq
COQBIN=

-include settings.sh


#######################################################

TLC_SRC=$(wildcard $(TLC)/*.v)
TLC_VO=$(TLC_SRC:.v=.vo)

FLOCQ_FOLDERS=$(addprefix $(FLOCQ)/src/,Core Calc Appli Prop)
FLOCQ_SRC=$(wildcard $(FLOCQ)/src/*/*.v)
FLOCQ_VO=$(FLOCQ_SRC:.v=.vo)
FLOCQ_INC=$(addprefix -I ,$(FLOCQ_FOLDERS))

-include flocq_inc_settings.sh
# If you have problem with the compilation of Flocq,
# create a file called flocq_inc_settings.sh and put in it:
# FLOCQ_INC=-R $(FLOCQ)/src Flocq

#######################################################

INCLUDES=-I . -I $(TLC) $(FLOCQ_INC) 
COQC=$(COQBIN)coqc $(INCLUDES)
COQDEP=$(COQBIN)coqdep $(INCLUDES)
OCAMLOPT=ocamlopt

#######################################################
# MAIN SOURCE FILES

JS_SRC=\
	Shared.v \
	JsSyntax.v \
	JsSyntaxAux.v \
	JsSemantics.v \
	JsSemanticsAux.v \
	JsWf.v \
	JsWfAux.v \
	JsExtra.v \
	JsSafety.v \
	JsScopes.v \
	JsInterpreter.v \
	JsInterpreterProofs.v \
	JsInterpreterExample.v \
	JsProvePrograms.v

JS_VO=$(JS_SRC:.v=.vo)


#######################################################
# EXTENSIONS

.PHONY: all depend clean
.SUFFIXES: .v .vo

#######################################################
# MAIN TARGETS

all: $(JS_VO) 

flocq: $(FLOCQ_VO)

tags: $(JS_SRC)
	./gentags.sh


#######################################################
# EXTERNAL LIBRARIES: TLC and Flocq

init: 
	svn checkout -r 214 svn://scm.gforge.inria.fr/svn/tlc/branches/v3.1 tlc
	tar -xzf flocq-2.1.0.tar.gz 
	mv flocq-2.1.0 flocq

# alternative: pull git from svn
#	git clone https://gforge.inria.fr/git/flocq/flocq.git flocq


#######################################################

.v.vo : .depend
	$(COQC) -I $(TLC) $<



#######################################################
# INTERPRETER

interpreter: js/JsInterpreter.vo
	$(OCAMLOPT) -I js -c js/interpreter.mli
	$(OCAMLOPT) -I js -c js/interpreter.ml
	$(OCAMLOPT) -I js -o js/interpreter js/interpreter.cmx


#######################################################
# DEPENDENCIES

DEPS=$(JS_SRC) $(TLC_SRC) $(FLOCQ_SRC)

depend: .depend

.depend : $(DEPS) Makefile
	$(COQDEP) $(DEPS) > .depend

ifeq ($(findstring $(MAKECMDGOALS),init depend clean clean_all),)
include .depend
endif


#######################################################
# CLEAN

clean:
	bash -c "rm -f *.{vo,deps,dot,glob,ml,mli,cmi,cmx}" || echo ok
	bash -c "rm -f .depend" || echo ok

clean_all: clean
	find . -iname "*.vo" -exec rm {} \;
	find . -iname "*.glob" -exec rm {} \;


#######################################################
# LOCAL: copy all flocq and tlc .vo files to the head folder

local:
	@$(foreach file, $(FLOCQ_VO), cp $(file) $(notdir $(file));)
	@$(foreach file, $(TLC_VO), cp $(file) $(notdir $(file));)



#######################################################
# TEMP

js/interpreter.ml: js/JsInterpreterExample.vo


#######################################################
# DEPRECATED

LAMBDA_TO_JS_NAMES=\
	Lambda.v \
	LambdaToJs.v

NEW_SYNTAX=\
	JsNewSyntax.v\
