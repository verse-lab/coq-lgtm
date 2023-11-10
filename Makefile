COQMFFLAGS := -Q . LGTM -arg "-w -implicits-in-term,-redundant-canonical-projection,-several-object-files,-ambiguous-paths,-implicit-core-hint-db,-file-no-extension,-custom-entry-overriden,-custom-entry-overridden,-deprecated-hint-without-locality,-deprecated-ident-entry,-deprecated-hint-rewrite-without-locality,-deprecated-instance-without-locality"

TLC_FILES := LibAxioms.v LibTactics.v LibEqual.v LibLogic.v LibOperation.v LibBool.v LibReflect.v LibProd.v LibSum.v LibRelation.v LibOrder.v LibNat.v LibEpsilon.v LibInt.v LibMonoid.v LibContainer.v LibOption.v LibWf.v LibList.v LibListExec.v LibListZ.v LibMin.v LibSet.v LibChoice.v LibUnit.v LibFun.v LibString.v LibCore.v LibSepTLCbuffer.v

THEORY_FILES := LibSummation.v LibListExt.v LibDotprod_float.v LibFunExt.v LibLabType.v

SEPLOG_FILES := LibSepFmap.v LibSepVar.v LibSepSimpl.v LibWP.v LibSepReference.v LibArray.v LibLoops.v NTriple.v Subst.v LibLoops_float.v

EXPERIMENTS_FILES := COO.v RL.v SV.v CSR.v Unary.v uCSR.v SV_float.v CSR_float.v Prelude.v

ALLVFILES := ${addprefix lib/theory/,${TLC_FILES}} \
	${addprefix lib/theory/,${THEORY_FILES}} \
	${addprefix lib/seplog/,${SEPLOG_FILES}} \
	${addprefix experiments/,${EXPERIMENTS_FILES}}

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
