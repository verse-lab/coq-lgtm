Set Implicit Arguments.
From SLF Require Import LibSepSimpl LibSepReference LibSepTLCbuffer.
From SLF Require Import Fun LabType LibSepReference LibWP Struct.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.
Global Open Scope hprop_scope.


Section Subst. 

Context {D1 D2 : Type}.

Lemma fsubst_single {A B C : Type} (f : A -> C) (x : A) (y : B):
  Fmap.fsubst (Fmap.single x y) f = Fmap.single (f x) y.
Proof.
  apply/fmap_extens=> ?.
  rewrite /fsubst /= /map_fsubst /map_indom.
  case: classicT.
  { move=> ?; case: (indefinite_description _)=> ?[<-].
    case: classicT=> //->; by case: classicT. }
  case: classicT=> //<- []; exists x; splits*.
  by case: classicT.
Qed.


Definition fsubst {A B C : Type} (fm : fmap A B) (p : A -> bool) (f : A -> C) :=
  fsubst (filter (fun x _ => p x) fm) f.


Context (p : D1 -> bool) (f : D1 -> D2).
Hypothesis inj: forall x y, p x -> p y -> f x = f y -> x = y.

Definition hfsubst (h : hheap D1) := fsubst h (fun x => p x.2) (fun x => (x.1, f x.2)).

Definition hsub (H : hhprop D1) :=
  fun h => 
    exists h', 
      hfsubst h' = h  /\
      H h' /\
      (forall x l, indom h' (x, l) -> p l).

Lemma indom_fsubst x l h : 
  indom (hfsubst h) (l, x) = 
  exists y, indom h (l, y) /\ p y /\ f y = x.
Proof.
  rewrite /hfsubst/fsubst Fmap.fsubst_valid_indom.
  extens; split=> [[][]? y|[]y].
  { case=> /=-[->]<- /[! @filter_indom]-[]/=; eexists; eauto. }
  by case=> ?[?]<-; exists (l, y); rewrite /= filter_indom.
Qed.

Arguments disjoint_inv_not_indom_both {_ _ _ _ _}.

Lemma disjoint_fsubst h1 h2 : 
  disjoint h1 h2 -> disjoint (hfsubst h1) (hfsubst h2).
Proof.
  move=> /disjoint_inv_not_indom_both Dj.
  apply/disjoint_of_not_indom_both=> -[l x].
  rewrite ?indom_fsubst=> -[?][]{}/Dj /[swap]-[]/inj inj1<-.
  by move=> /[swap]-[?][]/[swap]-[/inj1]/[swap]?->.
Qed.

Lemma filter_id (h : hheap D1) : 
  (forall x l, indom h (x, l) -> p l) ->
  filter (fun x _ => p x.2) h = h.
Proof.
  move=> IN. 
  apply/fmap_extens=> -[]x l.
  rewrite /filter /= /map_filter /=.
  case E: (fmap_data h (x, l))=> //; move: (IN x l) E.
  case: classicT=> // NP /[swap]; rewrite /indom /map_indom=> -> NP'.
  by case: NP; apply/NP'.
Qed.

Lemma fsubst_disjoint h1 h2 : 
  (forall x l, indom h1 (x, l) -> p l) ->
  (forall x l, indom h2 (x, l) -> p l) -> 
  disjoint (hfsubst h1) (hfsubst h2) -> disjoint h1 h2 .
Proof.
  move=> ??; rewrite /hfsubst /fsubst ?filter_id //.
  move/disjoint_inv_not_indom_both=> dj; apply/disjoint_of_not_indom_both.
  case=> l x; move: (dj (l, f x)); rewrite ?Fmap.fsubst_valid_indom=> + IN1 IN2.
  by case; exists (l, x).
Qed.

Lemma fsubst_union h1 h2 : 
  (forall x l, indom h1 (x, l) -> p l) ->
  (forall x l, indom h2 (x, l) -> p l) -> 
  disjoint h1 h2 ->
  hfsubst (h1 \u h2) = hfsubst h1 \u hfsubst h2.
Proof.
  move=> h1p h2p ?.
  have h12p: (forall x l, indom (h1 \u h2) (x, l) -> p l).
  { move=> ?? /[! indom_union_eq]-[]; autos*. }
  rewrite /hfsubst /fsubst ?filter_id //.
  rewrite (@fsubst_union_valid' unit) // => -[??][??]/=.
  { by move/h1p=> /[swap]/h1p/inj/[apply]/[swap]-[]->->->. }
  by move/h12p=> /[swap]/h12p/inj/[apply]/[swap]-[]->->->.
Qed.


(* Lemma disjoint *)

(* Lemma eval_fsubst h h' h1 ht hv fs: 
  (forall x, indom fs x -> p x) ->
  eval (fsubst fs p f) (hfsubst (h \u h')) ht (hfsubst (h1 \u h')) hv ->
  eval fs (h \u h') (ht \o f) (h1 \u h') (hv \o f).
Proof.
move=> ?. *)


Lemma eval_fsubst h h' h1 ht hv fs: 
  (forall x, indom fs x -> p x) ->
  eval (fsubst fs p f) (hfsubst (h \u h')) ht (hfsubst (h1 \u h')) hv ->
  eval fs (h \u h') (ht \o f) (h1 \u h') (hv \o f).
Proof.
Admitted.


Lemma htriple_hsub {D : Type} (fs : fset D1) (ht : D2 -> trm) 
    (H : hhprop D1) (Q : (D1 -> val) -> hhprop D1) :
  hlocal H fs -> 
  (forall hv, hlocal (Q hv) fs) ->
  (forall x, indom fs x -> p x) ->
  htriple (fsubst fs p f) ht (hsub H) (fun hv : D2 -> val => hsub (Q (hv \o f))) ->
    htriple fs (ht \o f) H Q.
Proof.
  move=> Hl Ql fsp htr H'.
  apply/baz=> h' h'l ?[h][?][Hh][->][Dj]->.
  set fh' := hfsubst h'.
  set fh  := hfsubst h .
  have?: forall (x : loc) (l : D1), indom h' (x, l) -> p l.
  { move=> > /h'l; autos*. }
  have?: forall (x : loc) (l : D1), indom h (x, l) -> p l.
  { by move=> > /(Hl _ Hh) /fsp. }
  case: (htr (= fh') (fh \u fh')).
  { exists fh fh'; do ? split=> //.
    { by exists h; splits*. }
    exact/disjoint_fsubst. }
  move=> ?[hv][]/[swap]-[?][?][][]h1[<-] [?]Qh1[->].
  set (fh1 := hfsubst h1).
  case=> dj-> ev. exists (h1 \u h') (hv \o f); split.
  { move: ev; rewrite /fh /fh' /fh1 -?fsubst_union //; first last.
    { exact/fsubst_disjoint. }
    exact/eval_fsubst. }
  exists h1 h'; do?split=> //.
  by apply/fsubst_disjoint=> // ?? /h'l/fsp.
Qed.

Lemma hstar_hsub H1 H2 : 
  hsub (H1 \* H2) = hsub H1 \* hsub H2.
Proof.
  extens=> fh; splits.
  { case=> ?[]/[swap]-[][h1][h2][?][?][?]-> h12p <-.
    have?: forall (x : loc) (l : D1), indom h1 (x, l) -> p l.
    { move=> *; apply/h12p; rewrite indom_union_eq; autos*. }
    have?: forall (x : loc) (l : D1), indom h2 (x, l) -> p l.
    { move=> *; apply/h12p; rewrite indom_union_eq; autos*. }
    exists (hfsubst h1) (hfsubst h2); splits.
    { exists* h1. }
    { exists* h2. }
    { exact/disjoint_fsubst. }
    by rewrite fsubst_union. }
   case=> ? [?][][h1][<-][?]h1p [][h2][<-][?]h2p [?]->.
   exists (h1 \u h2); splits.
   { by rewrite fsubst_union=> //; apply/fsubst_disjoint. }
   exists h1 h2; splits=> //.
   { exact/fsubst_disjoint. }
   by move=> > /[! indom_union_eq]-[/h1p|/h2p].
Qed.

Lemma hempty_hsub : 
  hsub \[] = \[].
Proof.
  extens=> ?; split.
  { case=> ? []<-[]/hempty_inv-> ?.
    by rewrite /hfsubst /fsubst filter_id // fsubst_empty. }
  move/hempty_inv->; exists (empty : hheap D1); splits=> //.
  by rewrite /hfsubst /fsubst filter_id // fsubst_empty.
Qed.

Lemma hsingle_hsub d a x : 
  hsub (x ~(d)~> a) = 
    if p d then x ~(f d)~> a else hsub (x ~(d)~> a).
Proof.
  case: ssrbool.ifP=> // pd.
  have?: forall (a : val) x0 l, indom (single (x, d) a) (x0, l) -> p l.
  { by move=> ??? /[! indom_single_eq]-[?<-]. }
  extens=> ?; split.
  { case=> ? []<-[]/(@hsingle_inv _ _ _)->.
    rewrite /hfsubst /fsubst filter_id // ?fsubst_single //=.
    by move=> ?? /[! indom_single_eq]-[?<-]. }
  move/(@hsingle_inv _ _ _)->; exists (single (x, d) a); splits=> //; autos*.
  rewrite /hfsubst /fsubst filter_id // ?fsubst_single //; autos*.
Qed.


Lemma hstar_fset_hsub {A : Type} (Hi : A -> hhprop D1) fs : 
  hsub (\*_(i <- fs) Hi i) = \*_(i <- fs) hsub (Hi i).
Proof.
  elim/fset_ind: fs.
  { by rewrite ?hbig_fset_empty hempty_hsub. }
  by move=> ?? IH ?; rewrite ?hbig_fset_update // hstar_hsub IH.
Qed.

Lemma hpure_hsub P : 
  hsub \[P] = \[P].
Proof.
  extens=> ?; split.
  { case=> ? []<-[]/hpure_inv[]?-> ?.
    by rewrite /hfsubst /fsubst filter_id // fsubst_empty. }
  case/hpure_inv=> ?->. exists (empty : hheap D1); splits=> //.
  by rewrite /hfsubst /fsubst filter_id // fsubst_empty.
Qed.

Lemma hstar_harray {A : Type} L l d : 
  hsub (harray_int L l d) = 
    if p d then harray_int L l (f d) else hsub (harray_int L l d).
Proof.
  case: ssrbool.ifP=> // pd.
  rewrite /harray_int /harray ?hcellsE ?hstar_hsub hpure_hsub /hheader hstar_fset_hsub.
  rewrite  hsingle_hsub pd.  do ? f_equal.
  { by extens; split=> -[]->. }
  by apply/fun_ext_1=> ?; rewrite hsingle_hsub pd.
Qed.

End Subst. 
