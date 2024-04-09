We thank the reviewers for their time and the insightful reviews.

Only the reviews A and C had explicit questions or technical concerns; we respond to them below. We have also incorporated all suggested changes in a new branch of the LGTM github repo [`pldi24AE`](https://github.com/verse-lab/coq-lgtm/tree/pldi24AE).

### Review A

> Line 548 mentions the Nest rule. I can not find it in the paper or in the artifact.

This is a typo in the paper. The rule that was meant is `Focus` rule. Application of this rule corresponds to a `xfocus` tactic in the proof script. This typo is already fixed in the final version of the paper

> In Fig. 13, the postcondition of spec_spmspv contains the precondition `Arrs` but the postcondition in lemma spmspv_spec only has `\Top`.

Thanks for pointing that out. That is a mismatch indeed. We use `\Top` here just for readability proposes. We have added a [comment](https://github.com/verse-lab/coq-lgtm/blob/e7d844cbe8ec58d41d86fe16cec80d09146804d5/experiments/uCSR.v#L192) with an explicit explanation.

### Review C

> I could not verify the exact resemblance of the mechanised results with the paper results.

In the `README` file we explicitly point to the location of mechanised versions for each rule presented in the paper. We ask reviewer to elaborate on this comment and provide the names of rules which cause questions. We will incorporate all clarifications in comments next to those rules in the Coq development. 

> Splitting this file into multiple files may improve the localisation of reusable results of the mechanisation. ... Also, the file needs some cleaning particularly removing a large number of commented (unused) Lemmas.

Please refer to the following [commit](https://github.com/verse-lab/coq-lgtm/commit/fa7e7756bc11ab59bc13d26cfc4a25b8b967fe0d) which applies suggested changes. In this commit we erase all commented (unused) lemmas as well as split `LibWP.v` into three different files (with size not lager than 5kLOC each) `LibHypHeap.v`, `LibWP.v` and `LibXWP.v`.

> In addition to pinpointing where the important results and proof rules can be found it would also be helpful to have more details about the overall structure of mechanisation in the README file.

In the [commit](https://github.com/verse-lab/coq-lgtm/commit/fa7e7756bc11ab59bc13d26cfc4a25b8b967fe0d) mentioned above the also elaborate on the structure of `lib/seplog` folder.

>  In particular, I could not find any description in `README` about the content of the folder “lib/theory”.

The content of this folder was fully adopted from the code attached to the [6th volume of Software Foundations](https://softwarefoundations.cis.upenn.edu/slf-current/index.html) which presents the simplified version of [CFML](https://gitlab.inria.fr/charguer/cfml2) framework. In particular this folder represents a subset of [TLC](https://github.com/charguer/tlc/tree/master/src) library, designed for a general purpose automation and standard library extension. For instance file `LibEqual.v` defines an [`extens`](https://github.com/verse-lab/coq-lgtm/blob/fa7e7756bc11ab59bc13d26cfc4a25b8b967fe0d/lib/theory/LibEqual.v#L87) tactic to exploit extensionality of various structures.  We use this tactic in many places, including [`disjoint_update`](https://github.com/verse-lab/coq-lgtm/blob/fa7e7756bc11ab59bc13d26cfc4a25b8b967fe0d/lib/seplog/LibSepFmap.v#L1873) lemma, to exercise the extensionality of finite mappings.  

Each file from this folder contains comments with extensible documentation. As that is not our contribution we do not comment on its structure. We have added a reface to TLC and 6th volume of Software Foundations to the README file.


