From SLF Require Import LibSepSimpl LibSepReference LibSepTLCbuffer.
From SLF Require Import Fun LabType LibSepReference LibWP Struct Loops.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Set Implicit Arguments.
(* Unset Strict Implicit.
Unset Printing Implicit Defensive. *)

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

Lemma fsubst_valid_eq {A B C : Type} (f : A -> C) (fm : fmap A B) (x : A) :
  indom fm x ->
  (forall x y, indom fm x -> indom fm y -> f x = f y -> x = y) ->
    fmap_data (fsubst fm f) (f x) = fmap_data fm x.
Proof.
  move=> v inj.
  rewrite /fsubst /= /map_fsubst.
  case: classicT=> pf.
  { case: (indefinite_description _); clear pf.
    by move=> > []/inj/[swap]?->. }
  case: (prop_inv (indom fm x))=> [?|/not_not_inv->] //.
  case: pf; by exists x.
Qed.

Lemma fsubst_valid_eq_fset {A C : Type} (f : A -> C) (fm : fset A) (x : A) :
  indom fm x ->
  (* (forall x y, indom fm x -> indom fm y -> f x = f y -> x = y) -> *)
    fmap_data (fsubst fm f) (f x) = fmap_data fm x.
Proof.
  move=> v.
  rewrite /fsubst /= /map_fsubst.
  case: classicT=> pf.
  { case: (indefinite_description _); clear pf.
    move=> ?[]?; move: v; rewrite /indom /map_indom.
    by do ? case: (fmap_data _ _)=> // -[]. }
  case: (prop_inv (indom fm x))=> [?|/not_not_inv->] //.
  case: pf; by exists x.
Qed.

Lemma fsubst_update_fset {A C : Type} (f : A -> C) (fm : fset A) x y: 
  fsubst (update fm x y) f = update (fsubst fm f) (f x) y.
Proof.
  (* move=> inj. *)
  (* have?: forall h : fmap A B, valid_subst' h f. move=> > /inj. /[apply]/[apply]->. *)
  apply/fmap_extens=> z.
  case: (prop_inv (f x = z))=> [<-|?].
  { rewrite fsubst_valid_eq_fset ?indom_update_eq /update/=/map_union; autos*.
    by do ? case:classicT. }
  rewrite {2}/update fmapU_nin1 ?indom_single_eq //.
  case: (prop_inv (indom (fsubst (update fm x y) f) z))=> [|/[dup]?].
  { rewrite fsubst_valid_indom=> -[]w []?.
    rewrite indom_update_eq=> -[?|]; subst=> // ?.
    rewrite ?fsubst_valid_eq_fset //.
    { rewrite /update /union /= /map_union; case: classicT=> // ?; by subst. }
    rewrite indom_union_eq; autos*. }
  rewrite fsubst_valid_indom=> ind'.
  rewrite ?fmapNone // fsubst_valid_indom=> -[w][?]?; subst; apply:ind'. 
  exists w; split=> //; rewrite indom_update_eq; eauto.
Qed.

Lemma fsubst_update {A B C : Type} (f : A -> C) (fm : fmap A B) x y: 
  (forall a b, indom (update fm x y) a -> indom (update fm x y) b -> f a = f b -> a = b) ->
  fsubst (update fm x y) f = update (fsubst fm f) (f x) y.
Proof.
  move=> inj.
  (* have?: forall h : fmap A B, valid_subst' h f. move=> > /inj. /[apply]/[apply]->. *)
  apply/fmap_extens=> z.
  case: (prop_inv (f x = z))=> [<-|?].
  { rewrite fsubst_valid_eq // /update ?fmapU_in1 ?indom_union_eq ?indom_single_eq /=; autos*.
    by do ? case:classicT. }
  rewrite {2}/update fmapU_nin1 ?indom_single_eq //.
  case: (prop_inv (indom (fsubst (update fm x y) f) z))=> [|/[dup]?].
  { rewrite fsubst_valid_indom=> -[]w []?.
    rewrite indom_update_eq=> -[?|]; subst=> // ?.
    rewrite ?fsubst_valid_eq // /update ?fmapU_nin1 // ?indom_single_eq; try eqsolve.
    { move=> > ?? /inj-> // /[! indom_update_eq]; autos*. }
    rewrite indom_union_eq; autos*. }
  rewrite fsubst_valid_indom=> ind'.
  rewrite ?fmapNone // fsubst_valid_indom=> -[w][?]?; subst; apply:ind'. 
  exists w; split=> //; rewrite indom_update_eq; eauto.
Qed.


Lemma fsubst_union {A B C} `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) : 
  (forall a b, indom (fm1 \u fm2) a -> indom (fm1 \u fm2) b -> f a = f b -> a = b) ->
  fsubst (fm1 \u fm2) f = fsubst fm1 f \u fsubst fm2 f.
Proof.
  elim/fmap_ind: fm1.
  { by rewrite fsubst_empty ?union_empty_l. }
  move=> fm ?? IH ? inj.
  rewrite -update_union_not_r' ?(fsubst_update) ?IH ?update_union_not_r' //.
  { move=> >; rewrite ?indom_union_eq=> *.
    apply/inj=> //; rewrite indom_union_eq indom_update_eq; autos*. }
  move=> *; apply/inj=> //; rewrite indom_union_eq; autos*.
Qed.

(* Lemma fsubst_disjoint {A B C} `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) : 
  (forall a b, indom (fm1 \u fm2) a -> indom (fm1 \u fm2) b -> f a = f b -> a = b) ->
  disjoint fm1 fm2 -> disjoint (fsubst fm1 f) (fsubst fm2 f).
Proof.
  elim/fmap_ind: fm1.
  { by rewrite fsubst_empty ?union_empty_l. }
  move=> fm ?? IH ? inj.
  rewrite -update_union_not_r' ?(fsubst_update) ?IH ?update_union_not_r' //.
  { move=> >; rewrite ?indom_union_eq=> *.
    apply/inj=> //; rewrite indom_union_eq indom_update_eq; autos*. }
  move=> *; apply/inj=> //; rewrite indom_union_eq; autos*.
Qed. *)


Lemma fsubst_remove {A B C : Type} (f : A -> C) (fm : fmap A B) x: 
  (forall a b, x = a \/ indom (fm) a -> x = b \/ indom (fm) b -> f a = f b -> a = b) ->
  remove (fsubst fm f) (f x) = fsubst (remove fm x) f.
Proof.
  move=> inj.
  (* have?: forall h : fmap A B, valid_subst' h f. move=> > /inj. /[apply]/[apply]->. *)
  apply/fmap_extens=> z.
  case: (prop_inv (f x = z))=> [<-|?].
  { rewrite ?fmapNone // ?indom_remove_eq; autos*.
    rewrite fsubst_valid_indom=> -[] ?[]/[swap].
    rewrite indom_remove_eq=> -[]/[swap]?/[swap]/inj->; autos*. }
  rewrite {1}/remove{1}/fmap_data /map_remove; case: classicT=> [?|_]; first eqsolve.
  case: (prop_inv (indom (fsubst (remove fm x) f) z)).
  { rewrite fsubst_valid_indom=> -[]w []?.
    rewrite indom_remove_eq=> -[]??; subst.
    rewrite ?fsubst_valid_eq //.
    { rewrite /remove /= /map_remove; case: classicT; eqsolve. }
    { rewrite* indom_remove_eq. }
    { move=> >; rewrite ?indom_remove_eq=> ?? /inj->; autos*. }
    move=> > ?? /inj->; autos*. }
  rewrite fsubst_valid_indom=> ind'.
  rewrite ?fmapNone // fsubst_valid_indom=> -[w][?]?; subst; apply: ind'.
  all: exists w; splits*; rewrite indom_remove_eq; eqsolve.
Qed. 

Lemma fsubst_hconseq {A B} (f : A ->B) (L : list val) p d :
  fsubst (hconseq L p d) (fun '(x, d0) => (x, f d0)) = hconseq L p (f d).
Proof.
  revert p d. induction L as [ | y L IH ]; intros.
  { by rewrite ! hconseq_nil fsubst_empty. }
  { rewrite ! hconseq_cons ?fsubst_union ?fsubst_single ?IH //.
    case=> ?? [] >; rewrite ?indom_union_eq ?indom_single_eq ?hconseq_indom.
    eqsolve. }
Qed.

Lemma fsubst_labf_of {A B : Type} (fs : fset A) l (f : A -> B) :
  fsubst (label (Lab l fs)) (labf_of f) = 
  label (Lab l (fsubst fs f)).
Proof.
  (* move=> /[dup]/labf_ofK ? c. *)
  elim/fset_ind: fs=> [|fs x].
  { by rewrite ?(label_empty, fsubst_empty). }
  rewrite label_update=> fE ?.
  rewrite ?fsubst_update_fset.
  by rewrite label_update fE.
Qed.

Lemma fsubst_indom {A B C : Type} (f : A -> C) (fm : fmap A B) x : 
  indom fm x -> indom (fsubst fm f) (f x).
Proof. by rewrite fsubst_valid_indom=> ?; exists*. Qed.

Lemma fsubst_indom_eq' {A B C : Type} (fs : fset A) (f : A -> C) (fm : fmap A B) (x : A) : 
  (forall x, indom fm x -> indom fs x) ->
  (forall x y, indom fs x -> indom fs y -> f x = f y -> x = y) ->
  indom fs x ->
  indom (fsubst fm f) (f x) = indom fm x.
Proof.
  move=> S > inj IN; extens; split=> [|/(@fsubst_indom _ _ _ _ _ _)]//.
  rewrite fsubst_valid_indom=> -[]?[]/inj /[swap]?<- //; exact/S.
Qed.

Arguments disjoint_inv_not_indom_both {_ _ _ _ _}.

Lemma fsubst_disjoint {A B C} `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) : 
  (forall a b, indom (fm1 \u fm2) a -> indom (fm1 \u fm2) b -> f a = f b -> a = b) ->
  disjoint fm1 fm2 -> disjoint (fsubst fm1 f) (fsubst fm2 f).
Proof.
  move=> inj /disjoint_inv_not_indom_both Dj.
  apply/disjoint_of_not_indom_both=> ?; rewrite ?fsubst_valid_indom.
  case=> ?[]<-?-[]?[]/inj E /[dup]?; rewrite E; first exact/Dj.
  all: rewrite* indom_union_eq.
Qed.

Lemma fsubst_disjoint' {A B C} `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) : 
  disjoint (fsubst fm1 f) (fsubst fm2 f) -> disjoint fm1 fm2.
Proof.
  move=> /disjoint_inv_not_indom_both Dj.
  apply/disjoint_of_not_indom_both=> *; apply/Dj; apply/fsubst_indom; eauto.
Qed.


Lemma fsubst_union_fset {A B : Type} (h1 h2 : fset A) (f : A -> B) : 
  disjoint h1 h2 ->
  fsubst (h1 \u h2) f = fsubst h1 f \u fsubst h2 f.
Proof.
  move=> ?.
  rewrite (@fsubst_union_valid' unit) // => ? >; last move: (_ \u _)=> ?.
  all: by rewrite /indom/map_indom; do ? case: (fmap_data _ _)=> // -[].
Qed.

Lemma fsubst_indom_eq {A B C : Type} (f : A -> C) (fm : hheap A) (x : A) fs p : 
  local fs fm ->
  (forall x y, indom fs x -> indom fs y -> f x = f y -> x = y) ->
  indom fs x ->
  indom (fsubst fm (fun '(x,d)=> (x, f d))) (p, f x) = indom fm (p, x).
Proof.
  move=> S > inj IN; extens; split=> [|/(@fsubst_indom _ _ _ _ _ _)]//.
  rewrite fsubst_valid_indom=> -[][]??[][]->/inj /[swap]?<- //. apply/S; eauto.
Qed.


Lemma fsubst_read_eq {A B C : Type} (f : A -> C) (fm : hheap A) (x : A) fs p : 
  local fs fm ->
  (forall x y, indom fs x -> indom fs y -> f x = f y -> x = y) ->
  indom fs x ->
  read (fsubst fm (fun '(x,d)=> (x, f d))) (p, f x) = read fm (p, x).
Proof.
  move=> S > inj IN; rewrite /fsubst /read /= /map_fsubst.
  case: classicT=> [?|].
  { case: (indefinite_description _)=> -[>][][->]/inj/[swap]?-> //.
    eapply S; eauto. }
  by case E: (fmap_data _ _)=> // -[]; exists (p, x); rewrite /map_indom E.
Qed.

Lemma local_preserv {D} h1 h2 (fs: fset D) ht hv d :
  indom fs d ->
  local fs h1 -> 
  eval1 d h1 ht h2 hv ->
    local fs h2.
Proof.
  move=> ?/[swap].
  elim=> //.
  { by move=> > ?? H12 ? H23 ? H34 /H12/H23/H34. }
  { by move=> > ? H12 ? H23 /H12/H23. }
  { by move=> > ? H12 ? H23 /H12/H23. }
  { by move=> *; rewrite /update local_union ;splits*=> ??; rewrite indom_single_eq=> -[]?<-. }
  { by move=> *; rewrite /update local_union ;splits*=> ??; rewrite indom_single_eq=> -[]?<-. }
  { move=> *; move=> >; rewrite indom_remove_eq=> -[]?; autos*. }
  { move=> > -> *; rewrite local_union; splits*=> ?? /(@hconseq_local _ _ _ _ _ _).
    by rewrite indom_single_eq=> <-. }
  move=> > -> ??; rewrite local_union; autos*.
Qed.

Lemma fsubstK {A B C : Type} (f : A -> B) (g : B -> A) (h : fmap A C) : 
  (forall x, indom h x -> g (f x) = x) ->
  Fmap.fsubst (Fmap.fsubst h f) g = h.
Proof. 
  elim/fmap_ind: h=> [|fm x y IH ? c].
  { by rewrite ?fsubst_empty. }
  do ? erewrite fsubst_update; eauto.
  { rewrite c ?IH // ?indom_update_eq; autos*.
    move=> *; apply/c; rewrite ?indom_update_eq; autos*. }
  { move=> >. rewrite -?fsubst_update.
    { by rewrite ?fsubst_valid_indom=> -[?][<-]/c->[?][<-]/c->->. }
    by move=> > /c {2}<-/c{2}<- ->. }
  by move=> > /c {2}<-/c{2}<- ->.
Qed.

Definition fsubst {A B C : Type} (fm : fmap A B) (fs : A -> Prop) (f : A -> C) :=
  fsubst (filter (fun x _ => fs x) fm) f.

Context (f : D1 -> D2) (fs : fset D1).
(* Context (p : D1 -> bool) (f : D1 -> D2). *)
Hypothesis inj: forall x y, indom fs x -> indom fs y -> f x = f y -> x = y.

Definition hfsubst (h : hheap D1) := fsubst h (fun x => indom fs x.2) (fun x => (x.1, f x.2)).

Definition hsub (H : hhprop D1) :=
  fun h => 
    exists h', 
      hfsubst h' = h  /\
      H h' /\
      local fs h'.

Lemma indom_fsubst x l h : 
  indom (hfsubst h) (l, x) = 
  exists y, indom h (l, y) /\ indom fs y /\ f y = x.
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
   local fs h ->
  filter (fun x _ => indom fs x.2) h = h.
Proof.
  move=> IN. 
  apply/fmap_extens=> -[]x l.
  rewrite /filter /= /map_filter /=.
  case E: (fmap_data h (x, l))=> //; move: (IN x l) E.
  case: classicT=> // NP /[swap]; rewrite /indom /map_indom=> -> NP'.
  by case: NP; apply/NP'.
Qed.

Lemma hfsubst_hconseq h1 h2 : 
  (forall x l, indom h1 (x, l) -> indom fs l) ->
  (forall x l, indom h2 (x, l) -> indom fs l) -> 
  disjoint (hfsubst h1) (hfsubst h2) -> disjoint h1 h2 .
Proof.
  move=> ??; rewrite /hfsubst /fsubst ?filter_id //.
  move/disjoint_inv_not_indom_both=> dj; apply/disjoint_of_not_indom_both.
  case=> l x; move: (dj (l, f x)); rewrite ?Fmap.fsubst_valid_indom=> + IN1 IN2.
  by case; exists (l, x).
Qed.

Lemma hfsubst_union h1 h2 : 
  (forall x l, indom h1 (x, l) -> indom fs l) ->
  (forall x l, indom h2 (x, l) -> indom fs l) -> 
  disjoint h1 h2 ->
  hfsubst (h1 \u h2) = hfsubst h1 \u hfsubst h2.
Proof.
  move=> h1p h2p ?.
  have h12p: (forall x l, indom (h1 \u h2) (x, l) -> indom fs l).
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

Arguments fsubst_indom {_ _ _ _ _ _}.

Lemma eval1_fsubst ht h h' (g : D2 -> D1) v d fs' : 
  local fs' h ->
  indom fs' d ->
  (forall x, indom fs' x -> g (f x) = x) ->
  eval1 (f d) (Fmap.fsubst h (fun '(x, d) => (x, f d))) (ht d) h' v ->
  eval1 d h (ht d) (Fmap.fsubst h' (fun '(x, d) => (x, g d))) v.
Proof.
  move=> l IN c1.
  rewrite -{-1}[d]c1 //.
  have: indom (Fmap.fsubst fs' f) (f d).
  { exact/fsubst_indom. }
  move: (f d) (ht _)=> {IN}d {}ht IN.
  rewrite -{2}[h] (fsubstK (fun '(x, d) => (x, f d)) (fun '(x, d) => (x, g d))); first last.
  { by case=> ?? /= /l/c1->. }
  have: local (Fmap.fsubst fs' f) (Fmap.fsubst h (fun '(x, d0) => (x, f d0))).
  { move=> >; rewrite ?fsubst_valid_indom.
    case=> -[]?? [][]?<-/l ?; exists*. }
  move: (Fmap.fsubst h _)=> {l}h.
  have : forall x y, indom (Fmap.fsubst fs' f) x -> indom (Fmap.fsubst fs' f) y -> g x = g y -> x = y.
  { move=> >; rewrite ?fsubst_valid_indom.
    by case=> ?[]<-?[]?[]<-? /[! c1] //->. }
  move: (Fmap.fsubst fs' f) IN=> {c1}fs' IN ginj /[swap].
  elim; try by intros; econstructor; eauto.
  { move=> > ? IH0 IH1 IH2 IH3 IH4 IH5 l. econstructor; autos*.
    { apply/IH3/local_preserv; eauto. }
    apply/IH5/local_preserv/IH2/local_preserv; eauto. }
  { move=> > ? IH0 IH1 IH2 l. econstructor; autos*.
    apply/IH2/local_preserv; eauto. }
  { move=> > ? IH0 IH1 IH2 l. econstructor; autos*.
    apply/IH2/local_preserv; eauto. }
  { move=> {}h {}v p min dm lh.
    erewrite fsubst_update; simpl; eauto.
    { apply/eval1_ref.
      { move=> ??; apply/min.
        move/fsubst_indom; autos*. }
      erewrite fsubst_indom_eq; eauto. }
     case=> ??[??]; rewrite ?indom_update_eq=> -[[<-<-][[<-<-]|]|]//.
     { by move/lh/ginj=> /[swap]-[<-]/(@eq_sym _ _ _)/[swap]/[apply]->. }
     move/lh/ginj/[swap]=> -[[]|/lh/[swap]/[apply]/[swap]-[]->->->] //.
     by move=><-<-/[swap]-[->]/[swap]/[apply]->. }
  { move=> {}h ?? dm ? l; apply/eval1_get; subst.
    { move/fsubst_indom: dm; exact. }
    erewrite fsubst_read_eq; eauto. }
  { move=> > dm lh. erewrite fsubst_update; eauto. 
    { apply/eval1_set.
      move/fsubst_indom: dm; exact. } 
    case=> ??[??]; rewrite ?indom_update_eq=> -[[<-<-][[<-<-]|]|]//.
    { by move/lh/ginj=> /[swap]-[<-]/(@eq_sym _ _ _)/[swap]/[apply]->. }
    move/lh/ginj/[swap]=> -[[]|/lh/[swap]/[apply]/[swap]-[]->->->] //.
    by move=><-<-/[swap]-[->]/[swap]/[apply]->. }
  { move=> > dm lh. rewrite -fsubst_remove; eauto.
    { apply/eval1_free.
      move/fsubst_indom: dm; exact. }
    case=> ??[??]; rewrite ?indom_update_eq=> -[[<-<-][[<-<-]|]|]//.
    { by move/lh/ginj=> /[swap]-[<-]/(@eq_sym _ _ _)/[swap]/[apply]->. }
    move/lh/ginj/[swap]=> -[[]|/lh/[swap]/[apply]/[swap]-[]->->->] //.
    by move=><-<-/[swap]-[]->->/(_ d)->. }
  { introv. intros -> -> Hn Hdj Hlfs lh.
    have?: forall a b : hloc D2,
    indom (LibSepReference.Fmap.hconseq (val_header k :: LibList.make k val_uninit) p d \u sa) a ->
    indom (LibSepReference.Fmap.hconseq (val_header k :: LibList.make k val_uninit) p d \u sa) b ->
    (let '(x, d0) := a in (x, g d0)) = (let '(x, d0) := b in (x, g d0)) -> a = b.
    { case=> ??[??]; rewrite 2?indom_union_eq ?hconseq_indom=> -[[->?][[<-?][]->|]|]//.
      { by move/lh/ginj=> /[swap]-[<-]/(@eq_sym _ _ _)/[swap]/[apply]->. }
      move/lh/ginj/[swap]=> -[[]|/lh/[swap]/[apply]/[swap]-[]->->->] //.
      by move=> -> ?/[swap]-[]->->/(_ d)->. }
    erewrite fsubst_union; eauto.
    { eapply eval1_alloc with (k:=k).
      2: reflexivity.
      2: unfolds null; intros HH; inversion HH; subst p; by apply Hn.
      { by apply fsubst_hconseq. }
      { apply/fsubst_disjoint=> // ??; rewrite union_comm_of_disjoint; eauto. }
      { unfold least_feasible_array_loc in *.
        intros p' Hdj' Hn'. apply Hlfs.
        2: unfolds null; intros HH; inversion HH; subst p'; by apply Hn.
        rewrite <- fsubst_hconseq in Hdj'; try assumption.
        apply/fsubst_disjoint'; eauto. }
    }
  }
  { introv. intros -> -> Hdj.
    rewrite local_union=> -[?] lh.
    have?: forall a b : hloc D2,
    indom (LibSepReference.Fmap.hconseq (val_header (length vs) :: vs) p d \u sa) a ->
    indom (LibSepReference.Fmap.hconseq (val_header (length vs) :: vs) p d \u sa) b ->
    (let '(x, d0) := a in (x, g d0)) = (let '(x, d0) := b in (x, g d0)) -> a = b.
    { case=> ??[??]; rewrite 2?indom_union_eq ?hconseq_indom=> -[[->?][[<-?][]->|]|]//.
      { by move/lh/ginj=> /[swap]-[<-]/(@eq_sym _ _ _)/[swap]/[apply]->. }
      move/lh/ginj/[swap]=> -[[]|/lh/[swap]/[apply]/[swap]-[]->->->] //.
      by move=> -> ?/[swap]-[]->->/(_ d)->. }
    erewrite fsubst_union; eauto.
    { eapply eval1_dealloc with (k:=length vs).
      2: reflexivity.
      1: eapply fsubst_hconseq; eauto.
      apply/fsubst_disjoint=> // ??; rewrite union_comm_of_disjoint; eauto. }
  }
  { introv. intros Hin Hhd lh. eapply eval1_length.
    { move/fsubst_indom: Hin; exact. }
    erewrite fsubst_read_eq; eauto.
  }
  Unshelve. all: exact unit.
Qed.

Lemma eval1_eq (d : D2) (d' : D1) h h' s s' t v : 
  d = f d' ->
  eval1 d (proj h d) t (proj h' d) v ->
  (forall l, fmap_data s (l, d') = fmap_data h (l, d)) -> 
  (forall l, fmap_data s' (l, d') = fmap_data h' (l, d)) ->
    eval1 d' (proj s d') t (proj s' d') v.
Proof.
  move=> dE ev sE s'E.
  set (g := (fun=> d') : D2 -> D1 ).
  have->: proj s' d' = Fmap.fsubst (proj h' d) (fun '(x, d) => (x, g d)).
  { apply/fmap_extens=> -[l' e].
    rewrite /Fmap.fsubst {2}/fmap_data /map_fsubst.
    case: classicT=> [?|].
    { case:(indefinite_description _)=> -[??][][]<-<-/=.
      rewrite /map_indom /= /map_filter.
      case: classicT=> [->|].
      { rewrite /g; case: classicT=> //.
        by rewrite s'E. }
      by case: (fmap_data _ _). }
    rewrite /proj /map_indom /filter /= /map_filter.
    case: classicT; last by case: (fmap_data s' _).
    move=>->; rewrite s'E.
    case E: (fmap_data h' (l', d))=> [x|] // -[].
    exists (l', d); splits*; rewrite E; by case: classicT. }
  apply/(eval1_fsubst (fun=>t) g (fs' := `{d'}))=> //.
  { exact/proj_local. }
  { by move=> ? /[! indom_single_eq]<-. }
  have<-: proj h d = Fmap.fsubst (proj s d') (fun '(x, d) => (x, f d)).
  { apply/fmap_extens=> -[l' e].
    rewrite /Fmap.fsubst {2}/fmap_data /map_fsubst.
    case: classicT=> [?|].
    { case:(indefinite_description _)=> -[??][][]<-<-/=.
      rewrite /map_indom /= /map_filter.
      case: classicT=> [->|].
      { rewrite -dE; case: classicT=> //.
        by rewrite sE. }
      by case: (fmap_data _ _). }
    rewrite /proj /map_indom /filter /= /map_filter.
    case: classicT; last by case: (fmap_data h _).
    move=>->; rewrite -sE.
    case E: (fmap_data s (l', d'))=> [x|] // -[].
    exists (l', d'); splits*; rewrite (E, dE) //; by case: classicT. }
  by rewrite -dE.
Qed.


Lemma eval_fsubst h h' h1 ht hv: 
  local fs h -> 
  local fs h1 -> 
  local fs h' ->
  eval (Fmap.fsubst fs f) (hfsubst (h \u h')) ht (hfsubst (h1 \u h')) hv ->
  eval fs (h \u h') (ht \o f) (h1 \u h') (hv \o f).
Proof.
  move=> lh lh1 lh' [IN OUT].
  split=> d ind /=.
  { have: indom (Fmap.fsubst fs f) (f d).
    { rewrite fsubst_valid_indom; exists*. }
    move/IN; rewrite /hfsubst/fsubst ?filter_id ?local_union //.
    move/(eval1_eq _ _ eq_refl)=> H. apply H=> ?.
    { have: local fs (h \u h'). 
      { rewrite* @local_union.  }
      move: (_ \u _)=> hh lhh.
      rewrite /Fmap.fsubst /= /map_fsubst; case: classicT.
      { move=> ?; case: (indefinite_description _)=> -[]/= >[][]->/inj/[swap]/lhh.
        by move/[swap]/[apply]->. }
      move=> NE; apply:not_not_inv=> IN'; apply/NE. 
      by eexists; splits*. }
    have: local fs (h1 \u h'). { rewrite* @local_union.  }
    move: (_ \u _)=> hh lhh.
    rewrite /Fmap.fsubst /= /map_fsubst; case: classicT.
    { move=> ?; case: (indefinite_description _)=> -[]/= >[][]->/inj/[swap]/lhh.
      by move/[swap]/[apply]->. }
    move=> NE; apply:not_not_inv=> IN'; apply/NE. 
    by eexists; splits*. }
  by rewrite ?(proj_empty (fs := fs)) // ?local_union.
Qed.


Lemma htriple_hsub (ht : D2 -> trm) 
    (H : hhprop D1) (Q : (D1 -> val) -> hhprop D1) :
  hlocal H fs -> 
  (forall hv, hlocal (Q hv) fs) ->
  htriple (Fmap.fsubst fs f) ht (hsub H) (fun hv : D2 -> val => hsub (Q (hv \o f))) ->
    htriple fs (ht \o f) H Q.
Proof.
  move=> Hl Ql htr H'.
  apply/baz=> h' h'l ?[h][?][Hh][->][Dj]->.
  set fh' := hfsubst h'.
  set fh  := hfsubst h .
  have?: forall (x : loc) (l : D1), indom h' (x, l) -> indom fs l.
  { move=> > /h'l; autos*. }
  have?: forall (x : loc) (l : D1), indom h (x, l) -> indom fs l.
  { by move=> > /(Hl _ Hh). }
  case: (htr (= fh') (fh \u fh')).
  { exists fh fh'; do ? split=> //.
    { by exists h; splits*. }
    exact/disjoint_fsubst. }
  move=> ?[hv][]/[swap]-[?][?][][]h1[<-] [?]Qh1[->].
  set (fh1 := hfsubst h1).
  case=> dj-> ev. exists (h1 \u h') (hv \o f); split.
  { move: ev; rewrite /fh /fh' /fh1 -?hfsubst_union //; first last.
    { exact/hfsubst_hconseq. }
    exact/eval_fsubst. }
  exists h1 h'; do?split=> //.
  by apply/hfsubst_hconseq=> // ?? /h'l/fsp.
Qed.
Lemma hstar_hsub H1 H2 : 
  hsub (H1 \* H2) = hsub H1 \* hsub H2.
Proof.
  extens=> fh; splits.
  { case=> ?[]/[swap]-[][h1][h2][?][?][?]-> h12p <-.
    have?: forall (x : loc) (l : D1), indom h1 (x, l) -> indom fs l.
    { move=> *; apply/h12p; rewrite indom_union_eq; autos*. }
    have?: forall (x : loc) (l : D1), indom h2 (x, l) -> indom fs l.
    { move=> *; apply/h12p; rewrite indom_union_eq; autos*. }
    exists (hfsubst h1) (hfsubst h2); splits.
    { exists* h1. }
    { exists* h2. }
    { exact/disjoint_fsubst. }
    by rewrite hfsubst_union. }
   case=> ? [?][][h1][<-][?]h1p [][h2][<-][?]h2p [?]->.
   exists (h1 \u h2); splits.
   { by rewrite hfsubst_union=> //; apply/hfsubst_hconseq. }
   exists h1 h2; splits=> //.
   { exact/hfsubst_hconseq. }
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
  indom fs d ->
  hsub (x ~(d)~> a) = x ~(f d)~> a.
Proof.
  move=> pd.
  have?: forall (a : val) x0 l, indom (single (x, d) a) (x0, l) -> indom fs l.
  { by move=> ??? /[! indom_single_eq]-[?<-]. }
  extens=> ?; split.
  { case=> ? []<-[]/(@hsingle_inv _ _ _)->.
    rewrite /hfsubst /fsubst filter_id // ?fsubst_single //=.
    by move=> ?? /[! indom_single_eq]-[?<-]. }
  move/(@hsingle_inv _ _ _)->; exists (single (x, d) a); splits=> //; autos*.
  rewrite /hfsubst /fsubst filter_id // ?fsubst_single //; autos*.
  all: by move=> ??; rewrite indom_single_eq=> -[?<-].
Qed.


Lemma hstar_fset_hsub {A : Type} (Hi : A -> hhprop D1) fs' : 
  hsub (\*_(i <- fs') Hi i) = \*_(i <- fs') hsub (Hi i).
Proof.
  elim/fset_ind: fs'.
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

Lemma harray_hsub L l d : 
  indom fs d ->
  hsub (harray_int L l d) = harray_int L l (f d).
Proof.
  move=> pd.
  rewrite /harray_int /harray ?hcellsE ?hstar_hsub hpure_hsub /hheader hstar_fset_hsub.
  rewrite  hsingle_hsub //.  do ? f_equal.
  { by extens; split=> -[]->. }
  by apply/fun_ext_1=> ?; rewrite hsingle_hsub //.
Qed.

End Subst. 

Lemma xntriple2_hsub {Dom Dom' : Type} (f : Dom -> Dom') 
  Pre Pre' Post (Post' : (labeled Dom' -> val) -> hhprop (labeled Dom')) i j 
  (C1 : Dom -> trm)
  (C2 : Dom -> trm) 
  (C1' : Dom' -> trm)
  (C2' : Dom' -> trm) 
  
  (fs1 fs2 : fset Dom)
  (F := labf_of f)
  (Fs := ⟨(i,0), fs1⟩ \u ⟨(j,0), fs2⟩) :
  i <> j ->
  (forall x y , indom Fs x -> indom Fs y -> F x = F y -> x = y) ->
  hlocal Pre Fs ->
  (forall hv, hlocal (Post hv) Fs) ->
  (forall x, C1 x = C1' (f x)) ->
  (forall x, C2 x = C2' (f x)) ->
  (hsub F Fs Pre = Pre') ->
  (forall (hv : labeled Dom' -> val), hsub F Fs (Post (hv \o F)) = Post' hv) ->
  {{ Pre' }}
    [{
      {i| ld in (Fmap.fsubst fs1 f) => C1' ld};
      {j| ld in (Fmap.fsubst fs2 f) => C2' ld}
    }]
  {{ hv, Post' hv }} ->

  {{ Pre }}
    [{
      {i| ld in fs1 => C1 ld};
      {j| ld in fs2 => C2 ld}
    }]
  {{ hv, Post hv }}.
Proof.
  move=> ? INj ?? C1E C2E <- /(@fun_ext_1 _ _ _ _)<-; rewrite /ntriple /nwp /= => ht.
  rewrite /htrm_of /=.
  set (g := fun ld : labeled Dom' => 
    If (i, 0) = lab (ld) /\ indom (Fmap.fsubst fs1 f) (el (ld)) then C1' (el (ld))
    else If (j, 0) = lab (ld) /\ indom (Fmap.fsubst fs2 f) (el (ld)) then C2' (el (ld))
    else 0).
  erewrite (wp_ht_eq _ (g \o F)).
  { rewrite wp_equiv /g/F. 
    apply/(@htriple_hsub (labeled Dom) (labeled Dom') F _ _ g).
    all: rewrite* union_empty_r.
    move: ht; rewrite /Fs/g wp_equiv union_empty_r ?fsubst_union_fset ?disjoint_label.
    { by rewrite /htrm_of /= ?fsubst_labf_of. }
    eqsolve. }
  case=> l d /=; rewrite /F/g //=.
  rewrite union_empty_r -?(indom_label_eq _ (Fmap.fsubst _ f)) -?fsubst_labf_of=> IND.
  rewrite ?(fsubst_indom_eq' (labf_of f) _ _ IND) // ?indom_label_eq ?C1E ?C2E //.
  all: move=> >; rewrite* indom_union_eq.
Qed.

Lemma foo {D} H1 H2 H3 H4 : H1 = H2 -> H3 = H4 -> H1 \* H3 = H2 \* H4 :> hhprop D.
by move=> ->->.
Qed.

Hint Rewrite @indom_label_eq @indom_union_eq @indom_prod : indomE.

Ltac indomE := autorewrite with indomE.

Ltac xsubst_rew H :=
  do ? match goal with 
  | |- hsub _ _ (hsingle _ _ _) = _ => erewrite hsingle_hsub; simpl; eauto
  | |- hsub _ _ (harray_int _ _ _) = _ => rewrite (@harray_hsub _ _ _ _ H); simpl; eauto
  | |- hsub _ _ (_ \* _) = _ => rewrite (@hstar_hsub _ _ _ _ H); apply/foo
  | |- hsub _ _ (@hbig_fset _ _ hstar _ _) = _ => 
    rewrite (@hstar_fset_hsub _ _ _ _ H); eapply hbig_fset_eq; intros ?; indomE=> ?
  | |- hsub _ _ \[] = _ => rewrite hempty_hsub; eauto
  | |- hsub _ _ \[_] = _ => rewrite hpure_hsub; eauto
  end.

Lemma hlocal_harray {D : Type} [L : list val] [p : loc] [d : D] fs: 
  indom fs d ->
  hlocal (harray L p d) fs.
Proof. by move=> ? ? /(@hlocal_harray _ _ _ _) l > /l/[!indom_single_eq]<-. Qed.


Ltac xlocal := 
  repeat (intros; 
  match goal with 
  | |- hlocal (_ \* _) _ => apply hlocal_hstar
  | |- hlocal \[] _    => apply hlocal_hempty
  | |- hlocal (hexists _) _ => apply hlocal_hexists
  | |- hlocal (hsingle _ _ _) (single _ _) => apply hlocal_hsingle_single
  | |- hlocal (hsingle _ _ _) (label (Lab _ (single _ _))) => 
    rewrite label_single; apply hlocal_hsingle_single
  | |- hlocal (hsingle _ _ _) _ =>
    apply hlocal_hsingle; indomE; autos*
  | |- hlocal (harray_int _ _ _) _ =>
    apply hlocal_harray; indomE; autos*
  | |- hlocal (hpure _) _ => apply hlocal_hpure
  | |- hlocal (@hbig_fset _ _ hstar _ _) _ => 
    apply hlocal_hstar_fset; intros ?; indomE; intros
  end).

Global Hint Rewrite @fsubst_single @prod_single_fsubst_snd : fsubstE.

Ltac fsubstE := autorewrite with fsubstE; simpl.

Tactic Notation "xsubst" uconstr(f) := 
  match goal with 
  | |- _ ==> N-WP [{
    [?i| _ in ?fs1 => _];
    [?j| _ in ?fs2 => _]
  }] {{ _ , _}} => 
    let Inj := fresh in 
    have Inj : 
      forall x y, 
        indom (⟨(i,0), fs1⟩ \u ⟨(j,0), fs2⟩) x -> 
        indom (⟨(i,0), fs1⟩ \u ⟨(j,0), fs2⟩) y -> 
        Lab (lab x) (f (el x)) = Lab (lab y) (f (el y)) -> x = y; 
        [ try (intros [?[??] ][?[??] ]; indomE=> /= + /[swap]=>/[swap]-[]->-> []?[]; eqsolve)
        | eapply (@xntriple2_hsub _ _ f); 
          [ by []
          | eapply Inj
          | xlocal 
          | xlocal
          | case=> ??/=; reflexivity
          | case=> ??/=; reflexivity
          | xsubst_rew Inj; indomE; autos*
          | move=> ? /=; xsubst_rew Inj; indomE; autos*
          |
          ]
        ]
  end; simpl; fsubstE.
