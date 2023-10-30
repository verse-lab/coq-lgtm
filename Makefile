COQMFFLAGS := -Q . SLF  -arg "-w -implicits-in-term,-redundant-canonical-projection,-several-object-files,-ambiguous-paths,-implicit-core-hint-db,-file-no-extension,-custom-entry-overriden,-custom-entry-overridden,-deprecated-hint-without-locality,-deprecated-ident-entry,-deprecated-hint-rewrite-without-locality,-deprecated-instance-without-locality"

ALLVFILES := Fun.v LabType.v LibAxioms.v LibTactics.v LibEqual.v LibLogic.v LibOperation.v LibBool.v LibReflect.v LibProd.v LibSum.v LibRelation.v LibOrder.v LibNat.v LibEpsilon.v LibInt.v LibMonoid.v LibContainer.v LibOption.v LibWf.v LibList.v LibListExec.v LibListZ.v LibMin.v LibSet.v LibChoice.v LibUnit.v LibFun.v LibString.v LibCore.v LibSepTLCbuffer.v LibSepFmap.v LibSepVar.v LibSepSimpl.v LibWP.v LibSepMinimal.v LibSepReference.v Sum.v Struct.v Unary.v ArrayDemo.v Loops.v COO.v RL.v Unary_IndexWithBounds.v SV.v CSR.v NTriple.v Subst.v Loops2.v Struct2.v uCSR.v ListCommon.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
