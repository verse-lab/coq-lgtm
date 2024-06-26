Set Implicit Arguments.
From LGTM.lib.theory Require Export LibCore LibSepTLCbuffer.
From LGTM.lib.seplog Require Export LibSepVar LibSepFmap.
From LGTM.lib.theory Require Import LibFunExt LibLabType.
From LGTM.lib.seplog Require Import LibSepSimpl LibSepReference LibHypHeap.

From mathcomp Require Import ssreflect ssrfun zify.

Open Scope Z_scope.

Global Hint Extern 1 (_ = _ :> hheap _) => fmap_eq.

(** At this point, the tactic [xsimpl] is defined. There remains to customize
    the tactic so that it recognizes the predicate [p ~~> v] in a special way
    when performing simplifications. *)

(** The tactic [xsimpl_hook_hsingle p v] operates as part of [xsimpl].
    The specification that follows makes sense only in the context of the
    presentation of the invariants of [xsimpl] described in [LibSepSimpl.v].
    This tactic is invoked on goals of the form [Xsimpl (Hla, Hlw, Hlt) HR],
    where [Hla] is of the form [H1 \* .. \* Hn \* \[]]. The tactic
    [xsimpl_hook_hsingle p v] searches among the [Hi] for a heap predicate
    of the form [p ~~> v']. If it finds one, it moves this [Hi] to the front,
    just before [H1]. Then, it cancels it out with the [p ~~> v] that occurs
    in [HR]. Otherwise, the tactic fails. *)

Ltac xsimpl_hook_hsingle p :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with (@hsingle _ p ?v') =>
      constr:(true) end);
  apply xsimpl_lr_cancel_eq;
  [ xsimpl_lr_cancel_eq_repr_post tt | ].

(** The tactic [xsimpl_hook] handles cancellation of heap predicates of the
    form [p ~~> v]. It forces their cancellation against heap predicates of
    the form [p ~~> w], by asserting the equality [v = w]. Note: this tactic
    is later refined to also handle records. *)

Ltac xsimpl_hook H ::=
  match H with
  | @hsingle _ ?p ?v => xsimpl_hook_hsingle p
  end.

(** One last hack is to improve the [lia] tactic so that it is able
    to handle the [val_int] coercion in goals and hypotheses of the
    form [val_int ?n = val_int ?m], and so that it is able to process
    the well-founded relations [dowto] and [upto] for induction on
    integers. *)

Ltac math_0 ::=
  unfolds downto, upto;
  repeat match goal with
  | |- val_int _ = val_int _ => fequal
  | H: val_int _ = val_int _ |- _ => inverts H
  end.

(* ################################################################# *)
(** * Reasoning Rules *)

Hint Resolve indom_single : core.

Section I_didnt_come_up_with_a_name.

Context {D : Type}.

Implicit Types P : Prop.
Implicit Types d : D.
Implicit Types (p : loc).
Implicit Types H : hhprop D.
(* Implicit Types Q : val->hhprop. *)

(* ================================================================= *)
(** ** Evaluation Rules for Primitives in Separation Style *)

(** These lemmas reformulated the big-step evaluation rule in a
    Separation-Logic friendly presentation, that is, by using disjoint
    unions as much as possible. *)

Lemma eval_ref_sep : forall s1 s2 v p d,
  s2 = Fmap.single (p, d) v ->
  (forall p', ~ Fmap.indom s1 (p', d) -> (p <= p')%Z) ->
  Fmap.disjoint s2 s1 ->
  @eval1 D d s1 (val_ref v) (Fmap.union s2 s1) (val_loc p).
Proof using.
  introv -> ? D'. forwards Dv: Fmap.indom_single p v.
  rewrite <- Fmap.update_eq_union_single. applys~ eval1_ref.
  intros N. applys~ Fmap.disjoint_inv_not_indom_both D' N.
Qed.

Lemma eval_get_sep : forall s s2 p d v,
  s = Fmap.union (Fmap.single (p, d) v) s2 ->
  eval1 d s (val_get (val_loc p)) s v.
Proof using.
  introv ->. forwards Dv: Fmap.indom_single p v.
  applys eval1_get.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_set_sep : forall s1 s2 h2 p d w v,
  s1 = Fmap.union (Fmap.single (p, d) w) h2 ->
  s2 = Fmap.union (Fmap.single (p, d) v) h2 ->
  Fmap.disjoint (Fmap.single (p, d) w) h2 ->
  eval1 d s1 (val_set (val_loc p) v) s2 val_unit.
Proof using.
  introv -> -> D'. forwards Dv: Fmap.indom_single p w.
  applys_eq eval1_set.
  { rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

Lemma eval_free_sep : forall s1 s2 v p d,
  s1 = Fmap.union (Fmap.single (p, d) v) s2 ->
  Fmap.disjoint (Fmap.single (p, d) v) s2 ->
  eval1 d s1 (val_free p) s2 val_unit.
Proof using.
  introv -> D'. forwards Dv: Fmap.indom_single p v.
  applys_eq eval1_free.
  { rewrite~ Fmap.remove_union_single_l.
    intros Dl. applys Fmap.disjoint_inv_not_indom_both D' Dl.
    applys Fmap.indom_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

Lemma local_partition_fset h (fs : fset D) :
  exists h1 h2 fs',
    local fs h1     /\
    local fs' h2    /\
    disjoint fs fs' /\
    disjoint h1 h2  /\ 
    h = h1 \u h2.
Proof.
  elim/fmap_ind: h fs.
  { move=> fs. 
    do ? apply/(ex_intro _ empty).
    by splits*=> //; rewrite union_empty_l. }
  move=> h [l d] y IHfs ? fs.
  case: (IHfs fs)=> h1 [h2] [fs'] [lc1][lc2][?][?]->.
  case: (prop_inv (indom fs d))=> dm.
  { have: ~ indom h2 (l, d).
    { move/lc2; apply/disjoint_inv_not_indom_both; eauto. }
    exists (update h1 (l, d) y), h2, fs'; splits=>//.
    { move=> >; rewrite indom_update_eq=> -[[_<-]|]; eauto. }
    { by rewrite disjoint_update. }
  by rewrite update_union_not_r. }
  have?: ~ indom h1 (l, d) by move/lc1.
  exists h1 (update h2 (l, d) y) (update fs' d tt); splits=> //.
  { move=> >; rewrite ?indom_update_eq=> -[[_<-]|/lc2]; autos*. }
  1,2: rewrite disjoint_comm disjoint_update; autos*.
  by rewrite update_union_not_l.
Qed.

Lemma local_partition h d :
  exists h1 h2,
    local (single d tt) h1 /\
    disjoint h1 h2         /\ 
    h = h1 \u h2.
Proof.
  case: (local_partition_fset h (single d tt))=> h1 [h2][fs]?.
  exists h1 h2; autos*.
Qed.

Lemma proj_union h1 h2 d : 
  proj (h1 \u h2) d = proj h1 d \u proj h2 d.
Proof.
  rewrite /proj filter_union' //.
  by case.
Qed.

Lemma proj_empty fs h d : 
  ~ indom fs d -> 
  local fs h -> 
  proj h d = empty.
Proof.
  move=> ? lc; apply/fmap_extens=> -[? d'].
  rewrite /empty {2}/fmap_data fmapNone // /proj filter_indom.
  by case=> /lc/[swap]->.
Qed.


Lemma proj_update h d l d' v : d <> d' -> 
  proj (update h (l, d) v) d' = proj h d'.
Proof.
  move=> ?; rewrite /update proj_union (@proj_empty (single d tt)) ?union_empty_l //.
  { by rewrite indom_single_eq. }
  by move=> >; rewrite ?indom_single_eq=> -[].
Qed.

Lemma proj_diff h1 h2 d : 
  proj (h1 \- h2) d = proj h1 d \- proj h2 d.
Proof.
  rewrite /diff /proj ?filter_filter.
  fequals; apply/fun_ext_2=> -[??] _.
  apply/prop_ext; split.
  { by case=>-> dm; split=> // /filter_indom []/dm. }
  case=> /[swap]-> dm; split=> // dm'; apply/dm/filter_indom.
  do ? split=> //; exact/0.
Qed.

Lemma proj_remove h d l d' : d <> d' -> 
  proj (Fmap.remove h (l, d)) d' = proj h d'.
Proof.
  move=> ?; rewrite remove_diff proj_diff (@proj_empty (single d tt) (single _ _)) ?diff_empty //.
  { by rewrite indom_single_eq. }
  by move=> >; rewrite ?indom_single_eq=> -[].
Qed.

Lemma proj_remove_eq h d l :
  proj (Fmap.remove h (l, d)) d = Fmap.remove (proj h d) (l, d).
Proof.
  rewrite remove_diff proj_diff update_empty {2}/proj filter_update=> [|[]//].
  by case: classicT=> //; rewrite filter_empty -update_empty -remove_diff.
Qed.

Lemma eval1_proj_nd d h h' t v : 
  eval1 d h t h' v -> 
  forall c, d <> c -> proj h c = proj h' c.
Proof.
  elim=> // >.
  { move=> ?? E1 ? E2 ? E3 *; by rewrite E1 // E2 // E3. }
  1-2: by move=> ? E1 ? E2 *; rewrite E1 // E2.
  all: move=> *; try by rewrite (proj_update, proj_remove).
  all: subst; rewrite proj_union.
  all: match goal with |- context[(proj ?hh _) \u _] => 
    rewrite -> proj_empty with (fs:=single d tt) (h:=hh) end; 
    try (by rewrite union_empty_l); try (by rewrite indom_single_eq).
  all: apply hconseq_local.
Qed.

Lemma hheap_eq_proj h1 h2 :
  (forall d, proj h1 d = proj h2 d) -> h1 = h2.
Proof.
  move=> e; apply/fmap_extens=> -[l d].
  move/(congr1 ((@fmap_data _ _)^~ (l, d))): (e d).
  rewrite /= /map_filter; case_if.
  by do ? case: fmap_data.
Qed.

Lemma proj_proj h d : 
  proj (proj h d) d = proj h d.
Proof.
  rewrite /proj filter_filter; fequals.
  apply/fun_ext_2=> -[*]; apply/prop_ext; splits*.
Qed.

Lemma proj_local {h d} : 
  local (single d tt) (proj h d).
Proof.
  move=> > /filter_indom[_  ]; by rewrite indom_single_eq.
Qed.

Lemma eval1_local (d : D) hd h h' t v fs :
  local (single d tt) hd ->
  local fs h ->
  ~ indom fs d ->
  disjoint hd h ->
  eval1 d (hd \u h) t h' v -> 
  exists hd', 
    local (single d tt) hd' /\
    h' = hd' \u h.
Proof.
  move=> lc lc' nd dj /eval1_proj_nd h'E.
  exists (proj h' d ); split.
  { exact/proj_local. }
  apply/hheap_eq_proj=> d'.
  case: (prop_inv (d = d'))=> [<-|/[dup]?/h'E<-].
  { by rewrite proj_union proj_proj (proj_empty nd lc') union_empty_r. }
  rewrite ?proj_union (proj_empty _ lc) ?indom_single_eq //.
  rewrite (proj_empty _ proj_local) ?indom_single_eq //.
Qed.

Lemma valid_subst_can {h : hheap D} {f g : D -> D} : 
  cancel f g -> valid_subst h (fun x => (x.1, f x.2)).
Proof. by move=> c1 [??][??]/=[->]/(can_inj c1)->. Qed.

Lemma valid_subst_disj_inv {A B C : Type} (fm1 fm2 : fmap A B) (f : A -> C) :
  valid_subst fm1 f ->
  valid_subst fm2 f ->
  disjoint (fsubst fm1 f) (fsubst fm2 f) ->
    disjoint fm1 fm2.
Proof.
  move=> v1 v2 + x=> /(_ (f x)).
  by rewrite ?fsubst_valid_eq.
Qed.

Lemma fsubst_hconseq_by_cancel (f g : D -> D) (Hc1 : cancel f g) (Hc2 : cancel g f) 
  (L : list val) p d :
  fsubst (hconseq L p d) (fun '(x, d0) => (x, g d0)) = hconseq L p (g d).
Proof.
  revert p d. induction L as [ | y L IH ]; intros.
  { by rewrite ! hconseq_nil fsubst_empty. }
  { rewrite ! hconseq_cons. 
    have [Hc1' Hc2']: 
      cancel (fun '(x, d) => (x : loc, g d)) (fun '(x, d) => (x, f d)) /\
      cancel (fun '(x, d) => (x : loc, f d)) (fun '(x, d) => (x, g d)).
    { by split; case=> ??; rewrite (Hc1, Hc2). }
    rewrite -> fsubst_union with (g:=(fun '(x, d0) => (x, f d0))); auto.
    rewrite -> fsubst_single with (g:=(fun '(x, d0) => (x, f d0))); auto.
    by rewrite -> IH.
  }
Qed.

Lemma eval1_fsubst ht h h' (f g : D -> D) v d : 
  cancel f g ->
  cancel g f ->
  eval1 (f d) (fsubst h (fun '(x, d) => (x, f d))) (ht d) h' v ->
  eval1 d h (ht d) (fsubst h' (fun '(x, d) => (x, g d))) v.
Proof.
  move=> c1 c2.
  rewrite -{-1}[d]c1; move: (f d) (ht _)=> {}d {}ht.
  have [c1' c2']: 
    cancel (fun '(x, d) => (x : loc, g d)) (fun '(x, d) => (x, f d)) /\
    cancel (fun '(x, d) => (x : loc, f d)) (fun '(x, d) => (x, g d)).
  { by split; case=> ??; rewrite (c1, c2). }
  rewrite -[h](fsubstK c1' c2') (fsubstK c2' c1').
  move: (fsubst h _)=> {}h.
  elim; try by intros; econstructor; eauto.
  { move=> {}h {}v p min dm.
    erewrite fsubst_update; eauto.
    apply/eval1_ref.
    { move=> ??; apply/min.
      by rewrite -(fsubst_indom _ _ c1' c2'). }
    by rewrite -(fsubst_indom _ _ c1' c2') in dm. }
  { move=> {}h ?? dm ?; apply/eval1_get; subst.
    { by rewrite -(fsubst_indom _ _ c1' c2') in dm. }
    by rewrite -(fsubst_read _ _ c1' c2'). }
  { move=> > dm. erewrite fsubst_update; eauto. 
    apply/eval1_set.
    by rewrite -(fsubst_indom _ _ c1' c2') in dm. }
  { move=> > dm; erewrite <-fsubst_remove; eauto.
    apply/eval1_free.
    by rewrite -(fsubst_indom _ _ c1' c2') in dm. }
  { introv. intros -> -> Hn Hdj Hlfs.
    erewrite fsubst_union; eauto.
    eapply eval1_alloc with (k:=k).
    2: reflexivity.
    2: unfolds null; intros HH; inversion HH; subst p; by apply Hn.
    { by apply fsubst_hconseq_by_cancel with (f:=f). }
    { eapply fsubst_disjoint; eauto. }
    { unfold least_feasible_array_loc in *.
      intros p' Hdj' Hn'. apply Hlfs.
      2: unfolds null; intros HH; inversion HH; subst p'; by apply Hn.
      rewrite <- fsubst_hconseq_by_cancel with (f:=f) in Hdj'; try assumption.
      apply valid_subst_disj_inv in Hdj'; auto.
      all: match goal with |- valid_subst _ ?ff => 
        replace ff with (fun x : hloc D => (x.1, g x.2)) end.
      2,4: extens; intros (?, ?); by simpl.
      all: eapply valid_subst_can; eauto.
    }
  }
  { introv. intros -> -> Hdj.
    erewrite fsubst_union; eauto.
    eapply eval1_dealloc with (k:=length vs).
    2: reflexivity.
    1: eapply fsubst_hconseq_by_cancel; eauto.
    eapply fsubst_disjoint; eauto.
  }
  { introv. intros Hin Hhd. eapply eval1_length.
    { by rewrite -(fsubst_indom _ _ c1' c2') in Hin. }
    by rewrite -(fsubst_read _ _ c1' c2') in Hhd. 
  }
Qed.

Lemma eval_fsubst (fs : fset D) ht h h' (f g : D -> D) hv :
  cancel f g ->
  cancel g f ->
  eval (fsubst fs f) (fsubst h (fun '(x, d) => (x, f d))) (ht \o g) h' hv ->
  eval fs h ht (fsubst h' (fun '(x, d) => (x, g d))) (hv \o f).
Proof.
  move=> c1 c2 [IN OUT]; split=> d IND.
  { rewrite (proj_fsubst _ _ c2 c1).
    move: (IN (f d)); rewrite (fsubst_indom _ _ c1 c2)=> /(_ IND).
    rewrite (proj_fsubst _ _ c1 c2) c1 /comp c1.
    exact/eval1_fsubst. }
  erewrite proj_fsubst=> //.
  move: (OUT (f d)). erewrite fsubst_indom=> // /(_ IND).
  erewrite proj_fsubst=> // <-.
  by rewrite fsubstK 1?c1 //; case=> ??; rewrite (c1, c2).
Qed.

(* ================================================================= *)
(** ** Hoare Reasoning Rules *)

(* ################################################################# *)
(** * Definition of total correctness Hoare Triples. *)

Definition hhoare (fs : fset D) (ht : D -> trm) (H : hhprop D) (Q: (D -> val) -> hhprop D) :=
  forall h, H h -> 
    exists h' hv, 
        eval fs h ht h' hv /\ Q hv h'.


Lemma proj_eqE h1 h2 d :
  (proj h1 d = proj h2 d) <->
  (forall l, fmap_data h1 (l, d) = fmap_data h2 (l, d)).
Proof.
  split; rewrite /proj.
  { move=> /[swap] l /(congr1 ((@fmap_data _ _)^~ (l, d))) /=.
    rewrite /map_filter. 
    do ? case: (fmap_data _ _)=> //; by case: classicT. }
  move=> hE; apply/fmap_extens=> -[l d'] /=; move: (hE l).
  rewrite /map_filter. case: classicT=> [->->|] //.
  by do ? case: (fmap_data _ _).
Qed.

Lemma eval1_eq d (d' : D) h h' s s' t v : 
  eval1 d (proj h d) t (proj h' d) v ->
  (forall l, fmap_data s (l, d') = fmap_data h (l, d)) -> 
  (forall l, fmap_data s' (l, d') = fmap_data h' (l, d)) ->
    eval1 d' (proj s d') t (proj s' d') v.
Proof.
  set (f x := If x = d' then d else If x = d then d' else x).
  have c: cancel f f.
  { move=> x; rewrite /f; do ? case: classicT=> //.
    by move<-. }
  move=> ev sE s'E.
  have->: proj s' d' = fsubst (proj h' d) (fun '(x, d) => (x, f d)).
  { apply/fmap_extens=> -[l' e].
    rewrite -{2}[e]c (fsubst_valid_eq (l', f e))=> [|[]??[]??[]->/(can_inj c)->]//.
    rewrite /f; case: classicT=> [->|]/=; rewrite /map_filter.
    { rewrite s'E; by do ? case:classicT. }
    do ? case: classicT=> //; try by (do ? case: (fmap_data _ _ )).
    by move=>->. }
  apply/(eval1_fsubst (fun=>t) (f := f) (g := f))=> //.
  have<-: proj h d = fsubst (proj s d') (fun '(x, d) => (x, f d)).
  { apply/fmap_extens=> -[l' e].
    rewrite -{2}[e]c (fsubst_valid_eq (l', f e))=> [|[]??[]??[]->/(can_inj c)->]//.
    rewrite /f. case: (classicT (e = d))=> [->|]/=; rewrite /map_filter.
    { rewrite -sE. (do ? case:classicT=> //). by move->. }
    do ? case: classicT=> //; try by (do ? case: (fmap_data _ _ )).
    by move=>->. }
  rewrite /f; by case: classicT.
Qed.


Lemma fsubst_valid_eq  {A B C : Type} (f : A -> C) (fm : fmap A B) (x : A) :
  valid_subst fm f -> 
    fmap_data (fsubst fm f) (f x) = fmap_data fm x.
Proof.
  move=> v.
  rewrite /fsubst /= /map_fsubst.
  case: classicT=> pf.
  { case: (indefinite_description _); clear pf.
    by move=> ? [/v]. }
  case: (prop_inv (indom fm x))=> [?|/not_not_inv->] //.
  case: pf; by exists x.
Qed.

Definition valid_subst' {A B C : Type} (fm : fmap A B) (f : A -> C) : Prop :=
  forall x1 x2, 
    indom fm x1 ->
    indom fm x2 ->
    f x1 = f x2 -> 
    fmap_data fm x1 = fmap_data fm x2.

Lemma fsubst_valid_indom  {A B C : Type} (f : A -> C) (fm : fmap A B) (x : C) :
    indom (fsubst fm f) x = 
    exists y, f y = x /\ indom fm y.
Proof.
  rewrite /fsubst /indom /= {1}/map_indom /map_fsubst.
  case: classicT=> pf.
  { case: (indefinite_description _); clear pf.
    move=> y [<-]?; extens; split=> //; eexists; eauto. }
  by extens.
Qed.

Lemma union_pair_eq_by_disjoint_raw {A B : Type} (fm1 fm2 fm3 fm4 : fmap A B)
  (Hdj1 : disjoint fm1 fm2) (Hdj2 : disjoint fm3 fm4)
  (Hjoin : forall x : A, indom fm1 x <-> indom fm3 x)
  (E : Fmap.map_union (Fmap.fmap_data fm1) (Fmap.fmap_data fm2) = 
    Fmap.map_union (Fmap.fmap_data fm3) (Fmap.fmap_data fm4)) : fm2 = fm4.
Proof.
  apply fmap_extens. intros x.
  pose proof (@disjoint_inv_not_indom_both _ _ _ _ x Hdj1) as Hdj1'.
  pose proof (@disjoint_inv_not_indom_both _ _ _ _ x Hdj2) as Hdj2'.
  specialize (Hjoin x).
  assert (indom fm2 x <-> indom fm4 x) as Hj'.
  { assert (indom (fm1 \u fm2) x <-> indom (fm3 \u fm4) x) as Htmp.
    { unfolds indom, map_indom. simpl. eqsolve. }
    rewrite ! indom_union_eq in Htmp. eqsolve.
  }
  unfolds indom, map_indom.
  destruct (fmap_data fm2 x) eqn:E1, (fmap_data fm4 x) eqn:E2; try eqsolve.
  apply f_equal with (f:=fun h => h x) in E.
  unfolds map_union.
  destruct (fmap_data fm1 x) eqn:?, (fmap_data fm3 x) eqn:?; try eqsolve.
Qed.

Corollary union_pair_eq_by_disjoint {A B : Type} (fm1 fm2 fm3 fm4 : fmap A B)
  (Hdj1 : disjoint fm1 fm2) (Hdj2 : disjoint fm3 fm4)
  (Hjoin : forall x : A, indom fm1 x <-> indom fm3 x)
  (E : fm1 \u fm2 = fm3 \u fm4) : fm2 = fm4.
Proof.
  unfolds union. inversion E. by apply union_pair_eq_by_disjoint_raw in H0.
Qed.

Lemma eval1_det h1 h2 ht d hv h2' hv' : 
  eval1 d h1 ht h2 hv ->
  eval1 d h1 ht h2' hv' ->
    h2 = h2' /\ hv = hv'.
Proof.
  move=> ev; elim: ev h2' hv'.
  all: intros; 
    match goal with 
    | H : eval1 _ _ _ _ _ |- _ => try by inversion H
    end.
  { inversion H6; subst. all: try by case: H=> /=.
    { case: (H1 _ _ H10)=> ??; subst.
      case: (H3 _ _ H12)=> ??; subst.
      by case: (H5 _ _ H15)=> ??; subst. }
    { inversion H0; subst; simpl in *; autos*.
      all: try by inversion H12.
      by inversion H12; inversion H13; subst. }
    inversion H0; subst; simpl in *; autos*=> //.
    inversion H13. }
  all: try by (inversion H2; subst=> //; simpl in *; autos*;
    case: H6=> *; subst; exact/H1).
  { inversion H3; subst; apply/H2; case: (H0 _ _ H7)=>-> //. }
  { inversion H3; subst; apply/H2; case: (H0 _ _ H10)=>->-> //. }
  { by inversion H1; subst; apply/H0. }
  { inversion H0; subst; simpl in *; autos*.
    all: try by inversion H; subst=> //.
    inversion H; inversion H6; subst; split=> //; by case: H5=>->. }
  { inversion H0; subst; simpl in *; autos*.
    all: try by inversion H; subst=> //.
    { inversion H4; subst; simpl in *; autos*.
      all: try by inversion H.
      inversion H; inversion H10; subst=> //. }
    inversion H; inversion H7; subst=> //; split=> //.
    all: try by case: H6 H8=> -> [->] //.
    all: try by case: H9 H10=> -> [->] //.
    { by injection H6=> -> ->; injection H8=> ->. }
    case: H9 H10 H1 H6=>-> [->] <-/eq_nat_of_eq_int-> //. }
  { inversion H1; subst=> //; simpl in *; autos*.
    { by inversion H7. }
    have-> //: (p = p0). 
    exact/eq_nat_of_eq_int/Z.le_antisymm/H3/H0/H. }
  { inversion H1; subst=> //; simpl in *; autos*.
    by inversion H7. }
  { inversion H0; subst=> //; simpl in *; autos*.
    { inversion H4; subst=> //; simpl in *; autos*.
      by inversion H10. }
    by inversion H7. }
  { inversion H0; subst=> //; simpl in *; autos*.
    by inversion H6. }
  { subst. inversion H4; subst; simpl in *; auto; try eqsolve.
    1: by inversion H8.
    assert (k = k0) as <- by lia.
    unfold least_feasible_array_loc in *.
    rewrite -> disjoint_comm in H2, H7.
    apply H3 in H7; try assumption.
    apply H9 in H2; try assumption.
    assert (p = p0 :> nat) as <- by lia.
    eqsolve.
  }
  { subst. inversion H2; subst; simpl in *; auto; try eqsolve.
    1: by inversion H6.
    split; try reflexivity.
    apply union_pair_eq_by_disjoint_raw in H; auto.
    intros (?, ?).
    (* test length *)
    apply f_equal with (f:=fun h => h (p, d)) in H.
    rewrite -> ! hconseq_cons in H. 
    simpl in H. unfolds map_union. case_if; try eqsolve.
    inversion H.
    rewrite -> ! hconseq_cons, -> ! indom_union_eq, 
      -> ! indom_single_eq, -> ! hconseq_indom.
    eqsolve.
  }
  { inversion H1; subst=> //; simpl in *; autos*.
    1: by inversion H7. eqsolve.
  }
Qed.

Lemma eval_valid_subst h h' (f : D -> D) fs hv ht :
  valid_subst h (fun x : loc * D => (x.1, f x.2)) -> 
  (forall d d', d <> d' -> f d = f d' -> indom fs d /\ indom fs d') ->
  eval fs h (ht \o f) h' hv ->
    valid_subst h' (fun x : loc * D => (x.1, f x.2)) /\
    (forall x y, f x = f y -> hv x = hv y).
Proof.
  move=> v fP [IN OUT]. 
  have v': valid_subst h' (fun x : loc * D => (x.1, f x.2)).
  { case=> ? d [l d'] [->]/[dup].
    case: (prop_inv (d = d'))=> [->|]//.
    move/fP/[apply]=> -[] /IN/= ev1 /IN /= ev2 fE.
    set (g x := If x = d' then d else If x = d then d' else x).
    have c: cancel g g.
    { move=> x; rewrite /g; do ? case: classicT=> //.
      by move<-. }
    have EQ: proj h d' = fsubst (proj h d) (fun '(x, d) => (x, g d)).
    { apply/fmap_extens=> -[l' e].
      rewrite -{2}[e]c (fsubst_valid_eq (l', g e))=> [|[]??[]??[]->/(can_inj c)->]//.
      rewrite /g; case: classicT=> [->|]/=; rewrite /map_filter.
      { rewrite (v (l', d) (l', d')); autos*.
        by do ? case: classicT. }
      do ? case: classicT=> //; try by (do ? case: (fmap_data _ _ )).
      by move=>->. }
    move: (eval1_fsubst (fun d => ht (f d)) (f := g) (g := g) (h := (proj h d)) (h' := (proj h' d'))).
    move/(_ (hv d') d c c); rewrite -EQ fE.
    have->: g d = d' by (rewrite /g; do ? case: classicT=> //).
    rewrite fE in ev1.
    move/(_ ev2)/eval1_det/(_ ev1)=> [] /(congr1 ((@fmap_data _ _)^~  (l, g d'))).
    rewrite (fsubst_valid_eq (l, d')).
    { have->: g d' = d by (rewrite /g; do ? case: classicT=> //).
      rewrite /proj /= /map_filter; do ? case: (fmap_data _ _)=> // >.
      all: do ? case: classicT=> //. }
    by case=> ??[??]/= [->]/(congr1 g)/[! c]->. }
  split=> // d1 d2/[dup].
  case: (prop_inv (d1 = d2))=> [->|]// /fP/[apply]-[].
  move/IN=> ev1 /IN/(eval1_eq d1 h h')/[swap]/[dup]/=fE <- ev2.
  suff: ((proj h' d1) = (proj h' d1)) /\ (hv d1 = hv d2) by case.
  apply/(eval1_det ev1 (ev2 _ _))=> ?; [apply/v|apply/v']=>/=; fequals.
Qed.

Lemma indom_fsubst {A B : Type} (fs : fset A) (f : A -> B) x : 
  indom (fsubst fs f) x = exists y, f y = x /\ indom fs y.
Proof. apply fsubst_valid_indom. Qed.

Lemma fmapNone {A B : Type} (fm : fmap A B) x :
  ~indom fm x ->
  fmap_data fm x = None.
Proof. by move/not_not_inv. Qed.

Lemma hhoare_hsub (fs : fset D) ht H Q f g : 
  (forall x, indom (fsubst fs f) x -> f (g x) = x) ->
  (forall hv hv', (forall x, indom fs x -> hv x = hv' x) -> Q hv = Q hv') ->
  (forall d d', d <> d' -> f d = f d' -> indom fs d /\ indom fs d') ->
  (forall x, indom (fsubst fs f) x <-> indom fs (g x)) ->
  hhoare fs (ht \o f) H Q ->
  hhoare (fsubst fs f) ht (hsub H f) (fun hv => hsub (Q (hv \o f)) f).
Proof.
  move=> c QP fP gP hh h Hh.
  case: Hh=> hf [<-][] v ?.
  case: (hh hf)=> // h'[hv][ev]?.
  case: (eval_valid_subst v fP ev)=> ? hvE.
  exists (fsubst h' (fun x => (x.1, f x.2))), (hv \o g); split.
  { case: ev=> IN OUT.
    split; move=> d ind.
    { move: ((gP _).1 ind)=> /IN /= /[! c] // ev.
      apply/(eval1_eq _ _ _ ev)=> l; rewrite -{1}[d]c //;
      exact/(fsubst_valid_eq (l, g d)). }
    rewrite ?proj_eqE=> l.
    case: (prop_inv (exists x, f x = d)).
    { case=> y/[dup]?<-. rewrite ?(fsubst_valid_eq (l, y)) //.
      move: (OUT y); rewrite proj_eqE=> -> // ind'; apply/ind.
      rewrite indom_fsubst; eexists; eauto. }
    move=> F. 
    rewrite ?fmapNone // fsubst_valid_indom // => -[][??]/= [][??]; subst;
    case: F; eexists; eauto. }
  eexists; splits; eauto. rewrite (QP _ hv)=> //.
  move=> x ? /=. 
  have: f x = f (g (f x)) by rewrite c // indom_fsubst; exists x.
  by move/hvE->.
Qed.

Local Notation hhprop := (hhprop D).

Lemma hhoare_hsubst (fs : fset D) ht H Q f g : 
  cancel f g -> 
  cancel g f ->
  hhoare (fsubst fs f) (ht \o g) (\{x |-> g x} H) (fun hv => \{x |-> g x} (Q (hv \o f))) ->
  hhoare fs ht H Q.
Proof.
  move=> c1 c2 hh h Hh.
  case: (hh (fsubst h (fun '(x, d) => (x, f d)))).
  { by rewrite /hsubst fsubstK // => -[??]; rewrite (c1, c2). }
  move=> h' [hv] [ev]; rewrite /hsubst=> Qh'.
  exists __, __, __; eauto.
  exact/eval_fsubst.
Qed.

Lemma eval_eq (fs : fset D) (ht1 ht2 : D -> trm) h h' hv : 
  (forall d, Fmap.indom fs d -> ht1 d = ht2 d) ->
  eval fs h ht1 h' hv -> eval fs h ht2 h' hv.
Proof.
  rewrite ?evalE=> E [??]; split=> // *; rewrite -E //; eauto.
Qed.

Lemma hhoare_eq (fs : fset D) (ht1 ht2 : D -> trm) H (Q: (D -> val) -> hhprop) : 
  (forall d, Fmap.indom fs d -> ht1 d = ht2 d) ->
  hhoare fs ht1 H Q -> hhoare fs ht2 H Q.
Proof.
  intros eq hh ? [h' [hv [ev ?] ] ]%hh.
  exists h', hv; splits~; applys~ eval_eq.
Qed.

Lemma hhoare_hv H Q fs ht : 
  hhoare fs ht H (fun hr => \exists hr', Q (hr \u_(fs) hr')) ->
  hhoare fs ht H Q.
Proof.
  move=> hh ? /hh[h'][hv][ev][hv']?.
  exists h', (hv \u_( fs) hv'); split=>//.
  by apply/eval_hv; eauto=> ?? /[! uni_in].
Qed.


Lemma hhoare0_dep ht H Q : 
  hhoare empty ht H Q = (H ==> \exists hv, Q hv).
Proof.
  apply/prop_ext; split.
  { move=> hh ? /hh[?][hv][][_] ev.
    move=> Qhv; exists hv; erewrite hheap_eq_proj; eauto. }
  move=> hq; apply/hhoare_hv=> h /hq [hv] ?.
  exists h, (fun (_ : D) => val_unit), __; try do ? eexists=> //.
  rewrite uni0; eauto.
Qed.

Lemma hhoare0 ht H Q : 
  hhoare empty ht H (fun=> Q) = (H ==> Q).
Proof.
  apply/prop_ext; split.
  { move=> hh ? /hh[?][?][][_] ev.
    apply: applys_eq_init; fequals.
    apply/hheap_eq_proj=> ?; exact/ev. }
  move=> hq h /hq ?; exists h, (fun (_ : D) => val_unit); by do ? split.
Qed.


Lemma eval_cup (fs1 fs2 : fset D) ht h1 h2 h3 hv1 hv2 : 
  disjoint fs1 fs2 ->
  eval fs1 h1 ht h2 hv1 ->
  eval fs2 h2 ht h3 hv2 ->
    eval (fs1 \u fs2) h1 ht h3 (hv1 \u_(fs1) hv2).
Proof.
  move=> disj; case=> ? E1[? E2]; splits*=> d.
  2: { rewrite indom_union_eq=> ?; rewrite* E1. }
  rewrite indom_union_eq=> -[] /[dup]/(disjoint_inv_not_indom_both disj) ??.
  { by rewrite -E2 // uni_in; auto. }
  by rewrite E1 // uni_nin; auto.
Qed.

Lemma hhoare_union (fs1 fs2 : fset D) ht H (Q Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  hhoare fs1 ht H Q ->
  (forall hv, 
    hhoare fs2 ht (Q hv) (fun hv' => Q' (hv \u_fs1 hv'))) -> 
    hhoare (fs1 \u fs2) ht H Q'.
Proof.
  intros disj hh1 hh2 ? [h1[ hv1 [? Qh1] ] ]%hh1.
  destruct (hh2 hv1 _ Qh1) as [h2 [hv2 [ev ?] ] ].
  exists h2, (hv1 \u_(fs1) hv2); split~.
  applys eval_cup; eauto.
Qed.

Definition insert {D} (fs : fset D) (fm1 fm2 : hheap D) : hheap D :=
  filter (fun '(_, d) _ => indom fs d) fm1 \+ filter (fun '(_, d) _ => ~indom fs d) fm2.

Lemma filter_false {A B : Type} (fm : fmap A B) (P : A -> B -> Prop):
  (forall x y, ~ P x y) -> 
  filter P fm = empty.
Proof.
  move=> np.
  apply/fmap_extens=> /= y; rewrite /map_filter.
  by case: (_ y)=> // ?; case: classicT=> // /np.
Qed.


Lemma insert_proj_in {A} (fs : fset A) (fm1 fm2 : hheap A) (d : A) :
  indom fs d -> proj (insert fs fm1 fm2) d = proj fm1 d.
Proof.
  move=> dm.
  rewrite /proj /insert filter_union'; last by case.
  rewrite ?filter_filter (filter_false fm2) ?union_empty_r.
  { fequals. apply/fun_ext_2=> -[]_ ? _.
    by apply/prop_ext; splits*=>->. }
  case=>* [->]; exact.
Qed.

Lemma insert_proj_nin {A} (fs : fset A) (fm1 fm2 : hheap A) (d : A) : 
  ~indom fs d -> proj (insert fs fm1 fm2) d = proj fm2 d.
Proof.
  move=> dm.
  rewrite /proj /insert filter_union'; last by case.
  rewrite ?filter_filter (filter_false fm1) ?union_empty_l.
  { fequals. apply/fun_ext_2=> -[]_ ? _.
    by apply/prop_ext; splits*=>->. }
  case=>* [->]; exact.
Qed.

Lemma insert_distr_union (fs : fset D) (h1 h2 h : hheap D):
  disjoint (filter (fun '(_, d) => fun=> ~ indom fs d) h1) h ->
  disjoint (filter (fun '(_, d) => fun=> indom fs d) h2) h ->
  insert fs h2 h1 \+ h = insert fs (h2 \+ h) (h1 \+ h).
Proof.
  move=> ??; rewrite /insert ?filter_union' //; try by case.
  rewrite union_assoc -[_ \+ _ \+ filter (fun '(_, d) => fun=> ~ indom fs d) h]union_assoc.
  rewrite [filter _ h  \+ _ ]union_comm_of_disjoint.
  { rewrite ?union_assoc -{1}(filter_union_compl h (fun '(_, d) => fun=> indom fs d)).
    do ? fequals. apply/fun_ext_2=> -[] //. }
  apply/disjoint_of_not_indom_both=> -[??] /filter_indom[_]?.
  by case/filter_indom=> _ [].
Qed.

Lemma eval_union_insert (fs1 fs2 : fset D) h1 h2 hv ht :
  disjoint fs1 fs2 ->
  eval (fs1 \u fs2) h1 ht h2 hv -> 
    eval fs1 h1 ht (insert fs1 h2 h1) hv /\ 
    eval fs2 (insert fs1 h2 h1) ht h2 hv.
Proof.
  move=> dj [IN OUT]; do ? split.
  { move=> d ?. 
    have->//: proj (insert fs1 h2 h1) d = proj h2 d.
    { by apply/insert_proj_in. }
    apply IN; rewrite* indom_union_eq. }
  { by move=> d ? /[! @insert_proj_nin]. }
  { move=> d I.
    have->//: proj (insert fs1 h2 h1) d = proj h1 d.
    { apply/insert_proj_nin/disjoint_inv_not_indom_both/I.
      autos*. }
    apply IN; rewrite* indom_union_eq. }
  move=> d ?.
  case: (prop_inv (indom fs1 d))=> ?.
  { exact/insert_proj_in. }
  rewrite insert_proj_nin //. 
  apply/OUT; rewrite* indom_union_eq.
Qed.

Lemma eval_cup2 (fs1 fs2 : fset D) h1 h2 hv ht: 
  disjoint fs1 fs2 -> 
  exists h', 
    forall h,
      disjoint (filter (fun '(_, d) => fun=> ~ indom fs1 d) h1) h -> 
      disjoint (filter (fun '(_, d) => fun=> indom fs1 d) h2) h -> 
      eval (fs1 \u fs2) (h1 \u h) ht (h2 \u h) hv -> 
        disjoint h h'                      /\ 
        eval fs1 (h1 \u h) ht (h' \u h) hv /\
        eval fs2 (h' \u h) ht (h2 \u h) hv /\
        h' = insert fs1 h2 h1.
Proof.
  move=> dj.
  exists (insert fs1 h2 h1)=> h H1 H2 /(eval_union_insert dj)[].
  rewrite -?insert_distr_union // => ??; splits=> //.
  rewrite disjoint_comm /insert disjoint_union_eq_l; splits*. 
Qed.

Lemma foo (fs : fset D) H Q ht :
  (forall h, hhoare fs ht (H \* (= h)) (Q \*+ (= h))) -> 
  (forall H', hhoare fs ht (H \* H') (Q \*+ H')).
Proof.
  move=> HH H' ? [h1] [h][?][?][?]->.
  case: (HH h (h1 \u h)).
  { exists h1, h; autos*. }
  move=> ? [hv][]/[swap]-[h'][?][?][->][?]-> ?.
  exists (h' \u h), hv; splits*.
  exists h', h; autos*.
Qed.

Lemma bar (fs : fset D) H Q ht :
  hhoare fs ht H Q <->
  (forall h, H h -> hhoare fs ht (= h) Q).
Proof.
  split=> hh ? /hh=> [|/(_ _ eq_refl)][h][hv][]??; exists h, hv; by subst.
Qed.

Lemma eval_frame h1 h2 h fs' (ht : D -> trm) (fs : fset D) hv: 
  eval fs h1 ht h2 hv ->
  local fs' h ->
  disjoint fs fs' ->
    eval fs (h1 \u h) ht (h2 \u h) hv.
Proof.
  case=> [IN OUT] lh dj.
  split=> d I; rewrite ?proj_union; last by rewrite ?OUT.
  apply/eval1_frame/IN=> // [??/filter_indom[/lh]|]; eauto.
  apply/disjoint_inv_not_indom_both; eauto.
Qed.

Lemma diff_union_distr {A B : Type} (h1 h2 h3 : fmap A B) :
  (h1 \- h2) \u (h3 \- h2) = (h1 \u h3) \- h2.
Proof.
  apply fmap_extens. intros x.
  unfold union, map_union, diff. simpl.
  unfold map_filter.
  destruct (fmap_data h1 x) eqn:E1, (fmap_data h2 x) eqn:E2, 
    (fmap_data h3 x) eqn:E3; repeat case_if; try eqsolve.
Qed.

Lemma disjoint_diff_refl {A B : Type} (h1 h2 : fmap A B) 
  (Hdj : disjoint h1 h2) : h1 \- h2 = h1.
Proof.
  apply fmap_extens. intros x.
  pose proof (@disjoint_inv_not_indom_both _ _ _ _ x Hdj).
  unfolds indom, map_indom. unfold diff, filter. simpl.
  unfold map_filter.
  destruct (fmap_data h1 x) eqn:E1, (fmap_data h2 x) eqn:E2; repeat case_if; try eqsolve.
Qed.

(* a special case of local_disjoint_disjoint *)
Lemma local_notin_disjoint fs h1 d (Hl : local fs h1) (Hni : ~ indom fs d)
  h2 (Hls : local (single d tt) h2) : disjoint h1 h2.
Proof.
  apply disjoint_of_not_indom_both.
  intros (p, dd). hnf in Hl, Hls. setoid_rewrite indom_single_eq in Hls.
  intros H1 H2. apply Hls in H2. apply Hl in H1. subst d. contradiction.
Qed.

Lemma disjoint_after_diff {A B : Type} (h1 h2 h3 : fmap A B) 
  (Hdj : disjoint h1 h2) : disjoint (h1 \- h3) h2.
Proof.
  apply disjoint_of_not_indom_both. intros x.
  rewrite diff_indom. move=> [H1 H2]. move: H1. by apply disjoint_inv_not_indom_both.
Qed.

Lemma eval1_part h1 h2 h fs ht d hv: 
  ~indom fs d ->
  eval1 d (h1 \u h) ht h2 hv -> 
  local fs h ->
  disjoint h1 h ->
  exists h2', h2 = h2' \u h /\ disjoint h2' h.
Proof.
  remember (h1 \u h) as h1h eqn: HE1.
  move=> +ev; move: ev h1 HE1.
  elim; intros; subst; (try by eexists; eauto).
  { case: (H1 h1)=> // s2'[E ?]; subst.
    case: (H3 s2')=> // s3'[??]; subst.
    case: (H5 s3')=> // s4'[??]; subst.
    by eexists; eauto. }
  1-2: try by (case: (H1 h1)=> // s2'[E ?]; subst;
    by eexists; eauto).
  1-2: (case: (H0 h1)=> // s2'[E ?]; subst;
    case: (H2 s2')=> // s3'[??]; subst;
    by eexists; eauto).
  try by (case: (H0 h1)=> // s2'[E ?]; subst;
    by eexists; eauto).
  all: try (have ?: ~ indom h (p, d) by (move/H2 || move/H1)).
  1-2: exists (update h1 (p, d) v); 
        rewrite update_union_not_r //; split=>//; 
        exact/disjoint_update_not_r.
  { exists (Fmap.remove h1 (p, d)).
    rewrite remove_union_not_r //; split=>//.
    exact/disjoint_remove_l. }
  { setoid_rewrite <- union_assoc. eexists. split. 1: reflexivity.
    rew_disjoint. split; auto.
  }
  { exists (h1 \- (Fmap.hconseq (val_header (length vs) :: vs) p d)).
    split.
    { replace h with (h \- hconseq (val_header (length vs) :: vs) p d).
      2:{
        apply disjoint_diff_refl.
        apply local_notin_disjoint with (fs:=fs) (d:=d); try assumption.
        apply hconseq_local.
      }
      rewrite -> diff_union_distr, <- HE1, <- diff_union_distr, -> diffxx, 
        -> disjoint_diff_refl; auto.
    }
    { by apply disjoint_after_diff. }
  }
Qed.

Lemma eval_part h1 h2 h (fs fs' : fset D) ht hv: 
  disjoint fs fs' ->
  eval fs (h1 \u h) ht h2 hv -> 
  local fs' h ->
  disjoint h1 h ->
  exists h2', h2 = h2' \u h /\ disjoint h2' h.
Proof.
  move=> dj [IN OUT] lh dj'.
  exists (h2 \- h); split; last exact/diff_disj.
  apply/hheap_eq_proj=> d. 
  rewrite proj_union proj_diff.
  case: (prop_inv (indom fs d)).
  { move/[dup]/IN; rewrite proj_union=> + ?. 
    case/(@eval1_part _ _ _ fs').
    { apply/disjoint_inv_not_indom_both; by eauto. }
    { by move=> ?? /filter_indom[/lh]. }
    { apply/disjoint_of_not_indom_both=> -[??].
      case/filter_indom=> /[swap] _ /[swap] /filter_indom[+ _].
      applys* disjoint_inv_not_indom_both. }
    move=> ? [->] ? /[! @union_diff]; autos*. }
  move/OUT<-; rewrite proj_union union_diff //.
  apply/disj_filter; rewrite disjoint_comm.
  applys* @disj_filter.
Qed.

Lemma read_union_l' [A B : Type] `{Inhab B} [h1 : fmap A B] (h2 : fmap A B) [x : A] :
  ~indom h2 x -> read (h1 \u h2) x = read h1 x.
Proof.
  case: h1 h2=> ?? [??]. 
  rewrite /indom /union /= /read /= /map_indom /map_union.
  by case: (_ x)=> [?[]//|?]; case: (_ x).
Qed.

Lemma union_eq_inv_of_locals_pre : forall h2 h2' h1 h1' (fs fs' : fset D),
  local fs h1 ->
  local fs h2 ->
  local fs' h1' ->
  local fs' h2' ->
  disjoint fs fs' ->
  h1 \u h1' = h2 \u h2' ->
  forall x v, fmap_data h1 x = Some v -> fmap_data h2 x = Some v.
Proof using.
  introv. intros Hl1 Hl2 Hl1' Hl2' Hdj HH. intros (l, d) v H.
  assert (fmap_data (h1 \u h1') (l, d) = Some v) as H'.
  { simpl. unfolds map_union. now rewrite -> H. }
  rewrite -> HH in H'. simpl in H'. unfolds map_union.
  destruct (fmap_data h2 (l, d)) as [ v' | ]; auto.
  unfolds local, disjoint, map_disjoint.
  assert (indom fs d) as Hc by (apply Hl1 with (x:=l); eqsolve).
  assert (indom fs' d) as Hc' by (apply Hl2' with (x:=l); eqsolve).
  specializes Hdj d. eqsolve.
Qed.

Lemma union_eq_inv_of_locals : forall h2 h2' h1 h1' (fs fs' : fset D),
  local fs h1 ->
  local fs h2 ->
  local fs' h1' ->
  local fs' h2' ->
  disjoint fs fs' ->
  h1 \u h1' = h2 \u h2' ->
  h1 = h2.
Proof using.
  introv. intros Hl1 Hl2 Hl1' Hl2' Hdj HH.
  apply fmap_extens. intros x.
  destruct (fmap_data h1 x) as [ v | ] eqn:E.
  { assert (fmap_data h2 x = Some v) by (apply union_eq_inv_of_locals_pre 
      with (fs:=fs) (fs':=fs') (h1:=h1) (h2:=h2) (h1':=h1') (h2':=h2'); auto).
    eqsolve.
  }
  { destruct (fmap_data h2 x) as [ v | ] eqn:E'; auto.
    assert (fmap_data h1 x = Some v) by (apply union_eq_inv_of_locals_pre 
      with (fs:=fs) (fs':=fs') (h1:=h2) (h2:=h1) (h1':=h2') (h2':=h1'); auto).
    eqsolve.
  }
Qed.

Fact local_single p d v : local (single d tt) (single (p, d) v).
Proof. unfolds local, indom, map_indom. simpl. intros. repeat case_if; subst; eqsolve. Qed.

Fact local_disjoint_disjoint (fs fs' : fset D) h1 h2 :
  local fs h1 -> local fs' h2 -> disjoint fs fs' -> disjoint h1 h2.
Proof.
  intros. unfolds local, indom, map_indom, disjoint, map_disjoint.
  intros (l, d). destruct (fmap_data h1 (l, d)) eqn:E1, (fmap_data h2 (l, d)) eqn:E2; auto.
  specialize (H l d). specialize (H0 l d). specialize (H1 d). eqsolve.
Qed.

Fact local_single_disjoint d fs h1 h2 :
  local fs h1 -> local (single d tt) h2 -> ~ indom fs d -> disjoint h1 h2.
Proof. 
  intros. apply local_disjoint_disjoint with (fs:=fs) (fs':=single d tt); try assumption.
  rewrite -> disjoint_comm. by apply disjoint_single_of_not_indom.
Qed.

Lemma union_eq_inv_of_locals' : forall h2 h2' h1 h1' (fs fs' : fset D),
  local fs h1 ->
  local fs h2 ->
  local fs' h1' ->
  local fs' h2' ->
  disjoint fs fs' ->
  h1 \u h1' = h2 \u h2' ->
  h1' = h2'.
Proof.
  introv. intros ? ? ? ? ?. 
  rewrite -> union_comm_of_disjoint with (h1:=h1), -> union_comm_of_disjoint with (h1:=h2).
  2-3: apply local_disjoint_disjoint with (fs:=fs) (fs':=fs'); assumption.
  rewrite -> disjoint_comm in H3.
  revert H1 H2 H H0 H3. apply union_eq_inv_of_locals.
Qed.

Lemma eval1_frame2 h1 h2 h fs ht d hv: 
  eval1 d (h1 \u h) ht (h2 \u h) hv -> 
  local fs h ->
  ~indom fs d ->
  disjoint h1 h ->
  disjoint h2 h ->
    eval1 d h1 ht h2 hv.
Proof.
  remember (h1 \u h) as h1h eqn: HE1.
  remember (h2 \u h) as h2h eqn: HE2.
  move=> ev; move: ev h1 h2 h HE1 HE2.
  elim; intros; subst; (try by econstructor; eauto).
  all: try have ?: h1 = h2 by (apply/union_eq_inv_of_disjoint; eauto).
  all: subst; try by econstructor.
  { case/(eval1_part H7): H0=> // ? [?]?; subst.
    case/(eval1_part H7): H2=> // ? [?]?; subst.
    econstructor=> //; [exact/H1|exact/H3|exact/H5]. }
  1-2: try by (case/(eval1_part H4): H=> // ? [?]?; subst;
    econstructor=> //; [exact/H0|exact/H2]).
  all: try have ?: ~ indom h (p, d) by (move/H0 || move/H1).
  all: try rewrite indom_union_eq in H.
  { move: HE2; rewrite update_union_not_r //.
    move/union_eq_inv_of_disjoint<-=> //.
    { applys* eval1_ref.
      { move=> ??; apply/H; rewrite* indom_union_eq. }
      rewrite* indom_union_eq in H0. }
    exact/disjoint_update_not_r. }
  { rewrite read_union_l' //; applys* eval1_get. }
  { move: HE2; rewrite update_union_not_r //.
    move/union_eq_inv_of_disjoint<-=> //.
    { applys* eval1_set. }
    exact/disjoint_update_not_r. }
  { move: HE2. rewrite- remove_union_not_r //.
    move/union_eq_inv_of_disjoint<-=> //.
    { applys* eval1_free. }
    exact/disjoint_remove_l. }
  { rewrite <- union_assoc in HE2. 
    apply union_eq_inv_of_disjoint in HE2.
    2-3: rew_disjoint; auto.
    subst h2.
    applys* eval1_alloc.
    hnf in H3 |- *. intros ? ?. apply H3. 
    rew_disjoint. split; try tauto.
    (* disjoint by local? *)
    rewrite disjoint_comm.
    apply local_notin_disjoint with (fs:=fs) (d:=d); try assumption.
    apply hconseq_local.
  }
  { rewrite <- union_assoc in HE1. 
    apply union_eq_inv_of_disjoint in HE1.
    2-3: rew_disjoint; auto.
    subst h1.
    applys* eval1_dealloc.
  }
  { destruct H; try contradiction.
    rewrite read_union_l in H0; try assumption.
    applys* eval1_length.
  }
Qed.

Lemma eval1_frame2_cancel h1 h2 h h' fs ht d hv: 
  eval1 d (h1 \u h) ht (h2 \u h') hv -> 
  local fs h ->
  local fs h' ->
  local (single d tt) h1 ->
  local (single d tt) h2 ->
  ~indom fs d ->
  disjoint h1 h ->
  disjoint h2 h' ->
  h = h'.
Proof.
  intros HH Hl Hl' Hl1 Hl2 Hnd Hdj1 Hdj2.
  rewrite -> union_comm_of_disjoint with (h1:=h1) in HH; auto.
  rewrite -> union_comm_of_disjoint with (h1:=h2) in HH; auto.
  remember (h \u h1) as h1' eqn:Eh1'. remember (h' \u h2) as h2' eqn:Eh2'.
  revert h1 h2 Eh1' Eh2' Hl1 Hl2 Hdj1 Hdj2.
  revert h h' Hl Hl'.
  assert (disjoint fs (single d tt)) as Hdj.
  { hnf. intros. unfolds indom, map_indom. simpl. case_if; subst; try eqsolve. destruct (fmap_data fs _); eqsolve. }
  induction HH; intros; subst.
  (* 0 *)
  all: try (apply union_eq_inv_of_locals with (fs:=fs) (fs':=single d tt) (h1':=h1) (h2':=h2); auto; fail).
  (* 1 *)
  all: try (eapply IHHH; eauto).
  (* 3 *)
  { rewrite -> union_comm_of_disjoint with (h1:=h) in HH1; auto.
    rewrite -> union_comm_of_disjoint with (h1:=h') in HH3; auto.

    pose proof (eval1_part Hnd HH1 Hl Hdj1) as (h2' & -> & Hdj2').
    pose proof (eval1_local Hl1 Hl Hnd Hdj1 HH1) as (h2'' & Hl2' & Htmp).
    apply union_eq_inv_of_disjoint in Htmp; try assumption.
    2:{ rewrite -> disjoint_comm. apply local_single_disjoint with (fs:=fs) (d:=d); assumption. }
    subst h2''.

    pose proof (eval1_part Hnd HH2 Hl Hdj2') as (h3' & -> & Hdj3').
    pose proof (eval1_local Hl2' Hl Hnd Hdj2' HH2) as (h3'' & Hl3' & Htmp).
    apply union_eq_inv_of_disjoint in Htmp; try assumption.
    2:{ rewrite -> disjoint_comm. apply local_single_disjoint with (fs:=fs) (d:=d); assumption. }
    subst h3''.

    eapply IHHH3.
    3: rewrite -> union_comm_of_disjoint; try reflexivity; assumption.
    3: reflexivity.
    all: assumption.
  }
  (* 2 *)
  { rewrite -> union_comm_of_disjoint with (h1:=h) in HH1; auto.
    rewrite -> union_comm_of_disjoint with (h1:=h') in HH2; auto.

    pose proof (eval1_part Hnd HH1 Hl Hdj1) as (h2' & -> & Hdj2').
    pose proof (eval1_local Hl1 Hl Hnd Hdj1 HH1) as (h2'' & Hl2' & Htmp).
    apply union_eq_inv_of_disjoint in Htmp; try assumption.
    2:{ rewrite -> disjoint_comm. apply local_single_disjoint with (fs:=fs) (d:=d); assumption. }
    subst h2''.

    eapply IHHH2.
    3: rewrite -> union_comm_of_disjoint; try reflexivity; assumption.
    3: reflexivity.
    all: assumption.
  }
  { rewrite -> union_comm_of_disjoint with (h1:=h) in HH1; auto.
    rewrite -> union_comm_of_disjoint with (h1:=h') in HH2; auto.

    pose proof (eval1_part Hnd HH1 Hl Hdj1) as (h2' & -> & Hdj2').
    pose proof (eval1_local Hl1 Hl Hnd Hdj1 HH1) as (h2'' & Hl2' & Htmp).
    apply union_eq_inv_of_disjoint in Htmp; try assumption.
    2:{ rewrite -> disjoint_comm. apply local_single_disjoint with (fs:=fs) (d:=d); assumption. }
    subst h2''.

    eapply IHHH2.
    3: rewrite -> union_comm_of_disjoint; try reflexivity; assumption.
    3: reflexivity.
    all: assumption.
  }
  (* special *)
  { unfold Fmap.update in Eh2'. 
    rewrite <- union_assoc, -> union_comm_of_disjoint with (h2:=h) in Eh2'.
    2:{ rewrite -> disjoint_comm. apply local_single_disjoint with (fs:=fs) (d:=d); try assumption. apply local_single. }
    rewrite -> union_assoc in Eh2'.
    apply union_eq_inv_of_locals with (fs:=fs) (fs':=single d tt) (h1':=Fmap.single (p, d) v \u h1) (h2':=h2); auto.
    rewrite -> local_union. split; try assumption. apply local_single.
  }
  { unfold Fmap.update in Eh2'. 
    rewrite <- union_assoc, -> union_comm_of_disjoint with (h2:=h) in Eh2'.
    2:{ rewrite -> disjoint_comm. apply local_single_disjoint with (fs:=fs) (d:=d); try assumption. apply local_single. }
    rewrite -> union_assoc in Eh2'.
    apply union_eq_inv_of_locals with (fs:=fs) (fs':=single d tt) (h1':=Fmap.single (p, d) v \u h1) (h2':=h2); auto.
    rewrite -> local_union. split; try assumption. apply local_single.
  }
  { rewrite -> union_comm_of_disjoint with (h1:=h) in Eh2'; auto.
    rewrite <- Fmap.remove_union_not_r in Eh2'.
    2:{ unfolds local, indom, map_indom. destruct (fmap_data h (p, d)) eqn:E; try eqsolve.
      specialize (Hl p d). eqsolve.
    }
    rewrite -> union_comm_of_disjoint with (h1:=h') in Eh2'.
    2: by rewrite disjoint_comm.
    apply union_eq_inv_of_locals' with (fs':=fs) (fs:=single d tt) (h1:=Fmap.remove h1 (p, d)) (h2:=h2); auto.
    unfolds local, indom, map_indom, Fmap.remove, Fmap.map_remove. intros l d0. 
    specialize (Hl1 l d0). simpls. repeat case_if; eqsolve. 
  }
  { rewrite -> union_comm_of_disjoint with (h1:=h) in Eh2'.
    2: by rewrite disjoint_comm.
    rewrite <- union_assoc in Eh2'.
    rewrite -> union_comm_of_disjoint with (h1:=h') in Eh2'.
    2: by rewrite disjoint_comm.
    apply union_eq_inv_of_locals' with (fs:=(single d tt)) (fs':=fs) in Eh2'; auto.
    rewrite local_union. split; auto. apply hconseq_local.
  }
  { rewrite <- union_assoc in Eh1'.
    rewrite -> union_comm_of_disjoint with (h2:=h') in Eh1'.
    2:{ 
      rewrite disjoint_comm. apply local_notin_disjoint with (fs:=fs) (d:=d); auto.
      apply hconseq_local.
    }
    rewrite -> union_assoc in Eh1'.
    apply union_eq_inv_of_locals with (fs':=(single d tt)) (fs:=fs) in Eh1'; auto.
    rewrite local_union. split; auto. apply hconseq_local.
  }
Qed.

Fact eval1_val_state_intact : forall d s1 s2 v vv, 
  eval1 d s1 (trm_val v) s2 vv -> s1 = s2.
Proof. intros. by inversion_clear H. Qed.

Lemma eval1_frame2' h1 h2 h h' fs ht d hv: 
  eval1 d (h1 \u h) ht (h2 \u h') hv -> 
  local fs h ->
  local fs h' ->
  local (single d tt) h1 ->
  local (single d tt) h2 ->
  ~indom fs d ->
  disjoint h1 h ->
  disjoint h2 h' ->
    eval1 d h1 ht h2 hv.
Proof.
  intros. pose proof H as Htmp.
  eapply eval1_frame2_cancel with (fs:=fs) in Htmp; try assumption. subst h'.
  revert H H0 H4 H5 H6. apply eval1_frame2.
Qed. 

Lemma eval_frame2 h1 h2 h fs' (ht : D -> trm) (fs : fset D) hv: 
  eval fs (h1 \u h) ht (h2 \u h) hv -> 
  local fs' h ->
  disjoint fs fs' ->
  disjoint h1 h ->
  disjoint h2 h ->
    eval fs h1 ht h2 hv.
Proof.
  move=> [IN OUT] lh d1 d2 d3.
  split.
  { move=> ? /[dup]DD {}/IN /[! proj_union] IN.
    apply/eval1_frame2; first exact/IN.
    { move=> ?? /filter_indom[/lh]; eauto. }
    { exact/disjoint_inv_not_indom_both/DD. }
    all: apply/disj_filter; rewrite disjoint_comm; applys* @disj_filter. }
  move=> ? /OUT /[! proj_union]/union_eq_inv_of_disjoint-> //.
  all: apply/disj_filter; rewrite disjoint_comm; applys* @disj_filter.
Qed.

Lemma eval_frame2' h1 h2 h h' fs' (ht : D -> trm) (fs : fset D) hv: 
  eval (fs \u fs') (h1 \u h) ht (h2 \u h') hv -> 
  local fs' h ->
  local fs' h' ->
  local fs h1 ->
  local fs h2 ->
  disjoint fs fs' ->
  disjoint h1 h ->
  disjoint h2 h' ->
    eval fs h1 ht h2 hv.
Proof.
  move=> [IN OUT] lh lh' lh1 lh2 d1 d2 d3.
  split.
  { move=> d DD.
    have{}/IN: indom (fs \u fs') d by rewrite* indom_union_eq.
    rewrite ?proj_union=> IN.
    apply/eval1_frame2'; first exact/IN.
    { move=> ?? /filter_indom[]/lh; eauto. }
    { move=> ?? /filter_indom[]/lh'; eauto. }
    { apply/proj_local. }
    { apply/proj_local. }
    { exact/disjoint_inv_not_indom_both/DD. }
    all: apply/disj_filter; rewrite disjoint_comm; applys* @disj_filter. }
  move=> d.
  case: (prop_inv (indom fs' d)).
  { move=> ind ind'.
    apply/fmap_extens=> -[]??; rewrite ?fmapNone // /proj filter_indom.
    { by case=> /[swap]->/lh2. }
    by case=> /[swap]->/lh1. }
  move=> ??.
  have /OUT: ~ indom (fs \u fs') d by rewrite* indom_union_eq.
  rewrite ?proj_union. 
  intros _. by rewrite -> ! proj_empty with (fs:=fs).
  (* apply/union_eq_inv_of_locals=> ??; rewrite filter_indom=> -[]/[swap]->; autos*. *)
Qed.

Lemma hhoare_proj (fs fs' : fset D) H H' (Q Q' : _ -> hhprop) ht : 
  disjoint fs fs' -> 
  hlocal H fs -> (forall hv, hlocal (Q hv) fs) -> 
  hlocal H' fs' -> (forall hv, hlocal (Q' hv) fs') -> 
  (exists h, H' h) ->
  hhoare (fs \u fs') ht (H \* H') (fun hv => Q hv \* Q' hv) ->
  hhoare fs ht H Q.
Proof.
  move=> dj lH lQ lH' lQ' [h' H'h] hh h /[dup]/lH lh Hh.
  case: (hh (h \u h')).
  { exists h h'; splits=> //.
    apply/disjoint_of_not_indom_both=> -[??] /lh/[swap].
    move/lH'=> /(_ H'h)/[swap].
    exact/disjoint_inv_not_indom_both. }
  move=> ? [hv] []/[swap]-[]h1[h1'][]/[dup]/lQ??[]/[dup]/lQ'??[]?->.
  move/eval_frame2'=> ev. exists h1 hv; splits=> //.
  apply/ev=> //. 
  { exact/lH'. }
  apply/disjoint_of_not_indom_both=> -[??] /lh/[swap]/lH'-/(_ H'h)/[swap].
  exact/disjoint_inv_not_indom_both.
Qed.

(* slightly easier to use *)
Lemma hhoare_proj' (fs fs' : fset D) H H' (Q Q' : _ -> hhprop) ht : 
  disjoint fs fs' -> 
  hlocal H fs -> (forall hv, hlocal (Q hv) fs) -> 
  hlocal H' fs' -> (forall hv, hlocal (Q' hv) fs') -> 
  (forall h, H h -> exists h', H' h') ->
  hhoare (fs \u fs') ht (H \* H') (fun hv => Q hv \* Q' hv) ->
  hhoare fs ht H Q.
Proof.
  move=> dj lH lQ lH' lQ' Himpl hh h /[dup]/lH lh Hh.
  specialize (Himpl _ Hh). move: Himpl => [h' H'h].
  case: (hh (h \u h')).
  { exists h h'; splits=> //.
    apply/disjoint_of_not_indom_both=> -[??] /lh/[swap].
    move/lH'=> /(_ H'h)/[swap].
    exact/disjoint_inv_not_indom_both. }
  move=> ? [hv] []/[swap]-[]h1[h1'][]/[dup]/lQ??[]/[dup]/lQ'??[]?->.
  move/eval_frame2'=> ev. exists h1 hv; splits=> //.
  apply/ev=> //. 
  { exact/lH'. }
  apply/disjoint_of_not_indom_both=> -[??] /lh/[swap]/lH'-/(_ H'h)/[swap].
  exact/disjoint_inv_not_indom_both.
Qed.

Lemma local_preserv h1 h2 (fs: fset D) ht hv :
  local fs h1 -> 
  eval fs h1 ht h2 hv ->
    local fs h2.
Proof.
  move=> lh [IN OUT] x d; apply: contrapose_inv=> /[dup] I /OUT /(congr1 (@fmap_data _ _)).
  move/(congr1 (@^~ (x, d))).
  have: ~indom h1 (x, d) by move/lh.
  case: (h1) (h2) I=> /= ?? [??].
  rewrite /proj /indom /= /filter /= /map_indom /map_filter /=.
  case: (_ (_, _))=> [??[]//|].
  case: (_ (_, _))=> // ?; by case: classicT.
Qed.

Lemma baz (fs : fset D) H Q ht :
  (forall h, local fs h -> hhoare fs ht (H \* (= h)) (Q \*+ (= h))) -> 
  (forall H', hhoare fs ht (H \* H') (Q \*+ H')).
Proof.
  move=> hh.
  apply/foo=> h'.
  apply/bar=> ? [h][?][?][->][?]-> ? ->.
  case: (local_partition_fset h' fs)=> h'1 [h'2] [fs'].
  case=> lh'1 [lh'2] [?] [?] E; subst. 
  move/(_ _ (h \u h'1)): (hh h'1)=> []//.
  { exists h, h'1; splits*. }
  move=>  h' [hv] [ev].
  exists (h' \u h'2) hv; splits.
  { rewrite -union_assoc; apply/eval_frame; by [|eauto|]. }
  suff: disjoint h' h'2.
  { case: b=> h'' [?][?][->][]?->; exists h'', (h'1 \u h'2); splits*. }
  case: (local_partition_fset h fs)=> h1 [h2] [fs''][lh1][lh2][d][?]?; subst.
  replace ((h1 \u h2) \u h'1) with ((h1 \u h'1) \u h2) in ev.
  { case/(eval_part d): (ev); [autos*|autos*|].
    move=> hx[?] ?; subst; rewrite disjoint_union_eq_l; split; last autos*.
    apply/disjoint_of_not_indom_both=> -[??] /lh'2 /[swap]?.
    case/(@disjoint_inv_not_indom_both _ _ _ fs _); autos*.
    apply/local_preserv; [|apply/eval_frame2;first exact/ev; eauto|]; eauto.
    by move=> ??; rewrite indom_union_eq=> -[/lh1|/lh'1]. }
  rewrite ?union_assoc; fequals; apply union_comm_of_disjoint.
  apply/disjoint_of_not_indom_both=> -[??] /lh'1/[swap]/lh2/[swap].
  exact/disjoint_inv_not_indom_both.
Qed.

Lemma eval_det h1 h2 ht (fs : fset D) hv h2' hv' : 
  eval fs h1 ht h2 hv ->
  eval fs h1 ht h2' hv' ->
    h2 = h2' /\ (forall d, indom fs d -> hv d = hv' d).
Proof.
  case=> IN1 OUT1 [] IN2 OUT2.
  split=> [|d].
  { apply/hheap_eq_proj=> d.
    case: (prop_inv (indom fs d))=> [|/[dup]/OUT1<-/OUT2] //.
    by move=>/[dup]/IN1/[swap]/IN2/eval1_det/[apply]-[]. }
  by move=> /[dup]/IN1/[swap]/IN2/eval1_det/[apply]-[].
Qed.

Lemma hhoare_union2_aux (fs1 fs2 : fset D) ht h h' (Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  local fs1 h' ->
  (forall H', hhoare (fs1 \u fs2) ht ((= h) \* H') (Q' \*+ H')) ->
    hhoare fs1 ht ((= h) \* (= h')) (fun hv => 
      \exists h'',
        (= h'') \*  (= h') \* \[
          forall h', local fs2 h' -> 
            hhoare fs2 ht ((= h'') \* (= h')) (fun hv' => Q' (hv \u_fs1 hv') \* (= h'))]
      ).
Proof.
  move=> dj lh' hh ? -[h1][h2][->][->][?]->.
  case/(_ (h \u h')): (hh (= h')).
  { by exists h, h'. }
  move=> ? [hv][] /[swap]-[he [?] ][?][->][?]-> ev.
  case: (eval_cup2 h he hv ht dj)=> // h'' HH.
  case: (HH h')=> //.
  1,2: rewrite disjoint_comm; applys* @disj_filter. 
  move=> d1 [ev1][ev2] h''E.
  exists (h'' \u h') hv; split=> //.
  exists h'', h'', h'; splits*. 
  exists h', (empty : hheap D); splits*.
  split=> // hi lhi ? [?][?][->][->][dji'']->.
  have ?: disjoint h hi.
  { subst. move: dji''. 
    rewrite /insert disjoint_union_eq_l=> -[_].
    move/(@disjoint_inv_not_indom_both _ _ _ _ _)=> Dj.
    apply/disjoint_of_not_indom_both=>-[? d] *.
    apply/Dj; eauto. apply/filter_indom; do ? split=> //; eauto.
    apply/disjoint_inv_not_indom_both/lhi; autos*. }
  case/(_ (h \u hi \u h')): (hh (= hi \u h')).
  { exists h (hi \u h'); autos*. }
  move=> ? [hv'] [/[swap] ][he'][?][?][->][?]-> ev'.
  case: (eval_cup2 h he' hv' ht dj)=> // h''' HH'.
  case: (HH' (hi \u h'))=> //.
  1,2: rewrite disjoint_comm; applys* @disj_filter. 
  move=> dji' [ev1'][ev2'] ?.
  have ?: disjoint h' hi.
  { apply/disjoint_of_not_indom_both=> -[??]. 
    move=> /lh'/[swap]/lhi. applys* disjoint_inv_not_indom_both. }
  move/eval_frame: ev1=> /(_ _ _ lhi dj).
  rewrite ?union_assoc (union_comm_of_disjoint h' hi) //.
  case/(eval_det ev1')=> /union_eq_inv_of_disjoint<-; autos*.
  move=> hvE.
  exists (he' \u hi), hv'; splits.
  { apply/eval_frame2; first (rewrite ?union_assoc; eauto).
    all: autos*. }
  exists he', hi; splits*.
  have->//: hv \u_(fs1) hv' = hv'.
  apply/fun_ext_1=> x.
  case: (prop_inv (indom fs1 x))=> ?.
  { by rewrite uni_in // hvE. }
  by rewrite uni_nin.
Qed.

Lemma hhoare_union_aux (fs1 fs2 : fset D) ht h h' (Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  local fs1 h' ->
  (forall H', hhoare (fs1 \u fs2) ht ((= h) \* H') (Q' \*+ H')) ->
    hhoare fs1 ht ((= h) \* (= h')) (fun hv => 
      \exists h'',
        (= h'') \*  (= h') \* \[
          forall h', local fs2 h' -> 
            hhoare fs2 ht ((= h'') \* (= h')) (fun hv' => Q' hv' \* (= h'))]
      ).
Proof.
  move=> dj lh' hh ? -[h1][h2][->][->][?]->.
  case/(_ (h \u h')): (hh (= h')).
  { by exists h, h'. }
  move=> ? [hv][] /[swap]-[he [?] ][?][->][?]-> ev.
  case: (eval_cup2 h he hv ht dj)=> // h'' HH.
  case: (HH h')=> //.
  1,2: rewrite disjoint_comm; applys* @disj_filter. 
  move=> d1 [ev1][ev2] h''E.
  exists (h'' \u h') hv; split=> //.
  exists h'', h'', h'; splits*. 
  exists h', (empty : hheap D); splits*.
  split=> // hi lhi ? [?][?][->][->][dji'']->.
  have ?: disjoint h hi.
  { subst. move: dji''. 
    rewrite /insert disjoint_union_eq_l=> -[_].
    move/(@disjoint_inv_not_indom_both _ _ _ _ _)=> Dj.
    apply/disjoint_of_not_indom_both=>-[? d] *.
    apply/Dj; eauto. apply/filter_indom; do ? split=> //; eauto.
    apply/disjoint_inv_not_indom_both/lhi; autos*. }
  case/(_ (h \u hi \u h')): (hh (= hi \u h')).
  { exists h (hi \u h'); autos*. }
  move=> ? [hv'] [/[swap] ][he'][?][?][->][?]-> ev'.
  case: (eval_cup2 h he' hv' ht dj)=> // h''' HH'.
  case: (HH' (hi \u h'))=> //.
  1,2: rewrite disjoint_comm; applys* @disj_filter. 
  move=> dji' [ev1'][ev2'] ?.
  have ?: disjoint h' hi.
  { apply/disjoint_of_not_indom_both=> -[??]. 
    move=> /lh'/[swap]/lhi. applys* disjoint_inv_not_indom_both. }
  move/eval_frame: ev1=> /(_ _ _ lhi dj).
  rewrite ?union_assoc (union_comm_of_disjoint h' hi) //.
  case/(eval_det ev1')=> /union_eq_inv_of_disjoint<-; autos*.
  move=> hvE.
  exists (he' \u hi), hv'; splits.
  { apply/eval_frame2; first (rewrite ?union_assoc; eauto).
    all: autos*. }
  exists he', hi; splits*.
Qed.

Lemma hhoare_conseq : forall ht H' hQ' H hQ fs,
  hhoare fs ht H' hQ' ->
  H ==> H' ->
  hQ' ===> hQ ->
  hhoare fs ht H hQ.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h. { applys* MH. }
  exists h' v. splits~. { applys* MQ. }
Qed.

Lemma hhoare_union2 (fs1 fs2 : fset D) ht H H' (Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  (forall H', hhoare (fs1 \u fs2) ht (H \* H') (Q' \*+ H')) ->
    hhoare fs1 ht (H \* H') (fun hv => (\exists Q,
      Q \* 
      \[forall H', hhoare fs2 ht (Q \* H') (fun hv' => Q' (hv \u_(fs1) hv') \* H')]) \* H').
Proof.
  move=> d hh.
  apply/baz=> hx lh.
  apply/bar=> h [?][?][Hx][->][?]->.
  apply/hhoare_conseq; first (apply/hhoare_union2_aux; [apply/d|apply/lh|]).
  { move=> P; apply/bar=> ?[?][?][->][?][?]->. 
    move/bar: (hh P); apply; do ? eexists; eauto. }
  { move=> ?->; do ? eexists; eauto. }
  move=> ?? [h'] [h1][h2][->][][h3][h4][->][][?] ? [?]->[?]->.
  exists (h' \u h4), hx; splits*.
  exists (= h'), h' , h4; splits*.
  split=> //.
  exact/baz.
Qed.

Lemma hhoare_union2' (fs1 fs2 : fset D) ht H H' (Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  (forall H', hhoare (fs1 \u fs2) ht (H \* H') (Q' \*+ H')) ->
    hhoare fs1 ht (H \* H') (fun hv => (\exists Q,
      Q \* 
      \[forall H', hhoare fs2 ht (Q \* H') (fun hv' => Q' hv' \* H')]) \* H').
Proof.
  move=> d hh.
  apply/baz=> hx lh.
  apply/bar=> h [?][?][Hx][->][?]->.
  apply/hhoare_conseq; first (apply/hhoare_union_aux; [apply/d|apply/lh|]).
  { move=> P; apply/bar=> ?[?][?][->][?][?]->. 
    move/bar: (hh P); apply; do ? eexists; eauto. }
  { move=> ?->; do ? eexists; eauto. }
  move=> ?? [h'] [h1][h2][->][][h3][h4][->][][?] ? [?]->[?]->.
  exists (h' \u h4), hx; splits*.
  exists (= h'), h' , h4; splits*.
  split=> //.
  exact/baz.
Qed.

Section Hoare1.

Context (d : D).

Implicit Type v : val.

Definition hoare (t:trm) (H:hhprop) (Q:val->hhprop) :=
  forall h, H h -> 
    exists h' v, eval1 d h t h' v /\ Q v h'.

(** Structural rules for [hoare] triples. *)

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h. { applys* MH. }
  exists h' v. splits~. { applys* MQ. }
Qed.


Lemma hoare_hexists : forall t (A:Type) (J:A->hhprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hhoare_hexists : forall ht (A:Type) (J:A->hhprop) Q fs,
  (forall x, hhoare fs ht (J x) Q) ->
  hhoare fs ht (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D'&U). destruct M1 as (M1&HP).
  lets E: @hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

Lemma hhoare_hpure : forall ht (P:Prop) H Q fs,
  (P -> hhoare fs ht H Q) ->
  hhoare fs ht (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D'&U). destruct M1 as (M1&HP).
  lets E: @hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

(** Other structural rules, not required for setting up [wpgen]. *)

Lemma hoare_hforall : forall t (A:Type) (J:A->hhprop) Q,
  (exists x, hoare t (J x) Q) ->
  hoare t (hforall J) Q.
Proof using.
  introv (x&M) Hh. applys* hoare_conseq (hforall J) Q M.
  applys* @himpl_hforall_l.
Qed.


Lemma hhoare_hforall : forall ht (A:Type) (J:A->hhprop) Q fs,
  (exists x, hhoare fs ht (J x) Q) ->
  hhoare fs ht (hforall J) Q.
Proof using.
  introv (x&M) Hh. applys* hhoare_conseq (hforall J) Q M.
  applys* @himpl_hforall_l.
Qed.

Lemma hoare_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  hoare t H Q ->
  hoare t (\[P] \-* H) Q.
Proof using. introv HP M. rewrite* @hwand_hpure_l. Qed.

Lemma hhoare_hwand_hpure_l : forall ht (P:Prop) H Q fs,
  P ->
  hhoare fs ht H Q ->
  hhoare fs ht (\[P] \-* H) Q.
Proof using. introv HP M. rewrite* @hwand_hpure_l. Qed.


(** Reasoning rules for [hoare] triples. These rules follow directly
    from the big-step evaluation rules. *)

Lemma hoare_eval_like : forall t1 t2 H Q,
  eval1_like d t1 t2 ->
  hoare t1 H Q ->
  hoare t2 H Q.
Proof using.
  introv E M1 K0. forwards (s'&v&R1&K1): M1 K0.
  exists s' v. split. { applys E R1. } { applys K1. }
Qed.

Lemma hhoare_eval_like : forall ht1 ht2 H Q fs,
  eval_like fs ht1 ht2 ->
  hhoare fs ht1 H Q ->
  hhoare fs ht2 H Q.
Proof using.
  introv E M1 K0. forwards (s'&v&R1&K1): M1 K0.
  exists s' v. split. { applys E R1. } { applys K1. }
Qed.


Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h K. exists h v. splits.
  { applys eval1_val. }
  { applys* M. }
Qed.

Lemma hhoare_val :  forall hv H Q fs,
  H ==> Q hv ->
  hhoare fs (fun d => trm_val (hv d)) H Q.
Proof using.
  introv M. intros h K. exists h hv. splits.
  { applys* eval_val. }
  { applys* M. }
Qed.

Lemma hoare_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  hoare (trm_fun x t1) H Q.
Proof using.
  introv M. intros h K. exists h __. splits.
  { applys~ eval1_fun. }
  { applys* M. }
Qed.

Lemma hhoare_fun : forall (x : D -> var) ht1 H Q fs,
  H ==> Q (fun d => val_fun (x d) (ht1 d)) ->
  hhoare fs (fun d => trm_fun (x d) (ht1 d)) H Q.
Proof using.
  move=> >. intros M h K. exists h __. splits.
  { applys* eval_fun. }
  { applys* M. }
Qed.

Lemma hoare_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof using.
  introv M. intros h K. exists h __. splits.
  { applys~ eval1_fix. }
  { applys* M. }
Qed.

Lemma hhoare_fix : forall (f x : D -> var) ht1 H Q fs,
  H ==> Q (fun d => val_fix (f d) (x d) (ht1 d)) ->
  hhoare fs (fun d => trm_fix (f d) (x d) (ht1 d)) H Q.
Proof using.
  move=> >. intros M h K. exists h __. splits.
  { applys* eval_fix. }
  { applys* M. }
Qed.

Lemma hhoare_fix_appapp2 : forall (f x : D -> var) ht1 H Q fs (t : val) t',
  hhoare fs (fun d => trm_seq t' ((trm_fix (f d) (x d) (ht1 d)) t)) H Q <->
  hhoare fs (fun d => trm_seq t' ((val_fix (f d) (x d) (ht1 d)) t)) H Q.
Proof.
  split; apply/hhoare_eval_like=> ??? [IN ?].
  { split=> // ? /IN ev. inversion ev; subst.
    apply/eval1_seq; eauto.
    inversion H6; subst. inversion H7; subst.
    inversion H4; by subst. }
  split=> // ? /IN ev. inversion ev; subst.
  apply/eval1_seq; eauto.
  by do ? (econstructor; eauto).
Qed.

Lemma hhoare_fix_app2 : forall (f x : D -> var) ht1 H Q fs (t : val),
  hhoare fs (fun d => (trm_fix (f d) (x d) (ht1 d)) t) H Q <->
  hhoare fs (fun d => (val_fix (f d) (x d) (ht1 d)) t) H Q.
Proof using.
  split.
  { move=> > M ? /M [h] [hv] [] [IN ?] ?.
    exists h, hv; do ? split=> //.
    move=> ? /IN; (do ? move: (proj _ _))=> ?? ev.
    inversion ev. 
    inversion H3; subst.
    by inversion H5; subst. }
  move=> > M ? /M [h] [hv] [] [IN ?] ?.
  exists h, hv; do ? split=> //.
  move=> ? /IN; (do ? move: (proj _ _))=> ?? ev.
  by do ? (econstructor; eauto).
Qed.

Lemma hhoare_fix_app2' : forall (f x : D -> var) ht1 H Q fs (t : _ -> val),
  hhoare fs (fun d => (trm_fix (f d) (x d) (ht1 d)) (t d)) H Q <->
  hhoare fs (fun d => (val_fix (f d) (x d) (ht1 d)) (t d)) H Q.
Proof using.
  split.
  { move=> > M ? /M [h] [hv] [] [IN ?] ?.
    exists h, hv; do ? split=> //.
    move=> ? /IN; (do ? move: (proj _ _))=> ?? ev.
    inversion ev. 
    inversion H3; subst.
    by inversion H5; subst. }
  move=> > M ? /M [h] [hv] [] [IN ?] ?.
  exists h, hv; do ? split=> //.
  move=> ? /IN; (do ? move: (proj _ _))=> ?? ev.
  by do ? (econstructor; eauto).
Qed.

Lemma hoare_app_fun : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  hoare (subst x v2 t1) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval1_app_fun E R1. } { applys K1. }
Qed.

Lemma hhoare_app_fun : forall hv1 hv2 (x : D -> var) ht1 H Q fs,
  (forall d, indom fs d -> hv1 d = val_fun (x d) (ht1 d)) ->
  hhoare fs (fun d => subst (x d) (hv2 d) (ht1 d)) H Q ->
  hhoare fs (fun d => trm_app (hv1 d) (hv2 d)) H Q.
Proof.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval_app_fun E R1. } { applys K1. }
Qed.

Lemma hoare_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval1_app_fix E R1. } { applys K1. }
Qed.

Lemma hhoare_app_fix : forall hv1 hv2 (f x : D -> var) ht1 H Q fs,
  (forall d, indom fs d -> hv1 d = val_fix (f d) (x d) (ht1 d)) ->
  hhoare fs (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (ht1 d))) H Q ->
  hhoare fs (fun d => trm_app (hv1 d) (hv2 d)) H Q.
Proof using.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval_app_fix E R1. } { applys K1. }
Qed.

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval1_seq R1 R2. }
Qed.

Lemma hhoare_seq : forall ht1 ht2 H Q H1 fs,
  hhoare fs ht1 H (fun hr => H1) ->
  hhoare fs ht2 H1 Q ->
  hhoare fs (fun d => trm_seq (ht1 d) (ht2 d)) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_seq R1 R2. }
Qed.

Lemma hoare_let : forall x t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v1, hoare (subst x v1 t2) (Q1 v1) Q) ->
  hoare (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval1_let R2. }
Qed.

Lemma hhoare_let : forall (x : D -> var) ht1 ht2 H Q Q1 fs,
  hhoare fs ht1 H Q1 ->
  (forall hv1, hhoare fs (fun d => subst (x d) (hv1 d) (ht2 d)) (Q1 hv1) Q) ->
  hhoare fs (fun d => trm_let (x d) (ht1 d) (ht2 d)) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_let R2. }
Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* eval1_if. }
Qed.

Lemma hhoare_if : forall (b: D -> bool) ht1 ht2 H Q fs,
  hhoare fs (fun d => if b d then ht1 d else ht2 d) H Q ->
  hhoare fs (fun d => trm_if (b d) (ht1 d) (ht2 d)) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* eval_if. }
Qed.


(** Operations on the state. *)

From mathcomp Require Import ssrnat.

Lemma ex_min (P : nat -> Prop) : (exists x, P x) -> exists x, P x /\ forall y, P y -> (x <= y)%Z.
Proof.
  case. elim/lt_wf_rect=> n IH.
  case: (prop_inv (exists x : nat, P x /\ (x < n)%coq_nat)).
  { by case=> ?[]/IH/[apply]. }
  move=> F ?; exists n; splits*=> y?.
  apply:not_not_inv=> ?; case: F; exists y; split=> //; lia.
Qed.

Lemma single_fresh' : forall (h : hheap D) v,
  exists l, 
    Fmap.disjoint (single (l, d) v) h.
Proof using.
  move=> h v.
  set (h' := fsubst (proj h d) fst).
  case: (exists_fresh 0%nat h')=> x [].
  rewrite /h' fsubst_valid_indom=> ind ?.
  exists x.
  apply/disjoint_of_not_indom_both=> -[]??.
  rewrite indom_single_eq=> -[]<-<- ?; case: ind.
  exists (x, d); split=> //; rewrite /proj filter_indom; autos*.
Qed.

Lemma single_fresh (h : hheap D) v :
  exists l, 
    Fmap.disjoint (single (l, d) v) h /\ 
    (forall p', ~ Fmap.indom h (p', d) -> (l <= p')%Z).
Proof using.
  case/ex_min: (single_fresh' h v)=> l []? min.
  exists l; split=> // l' ?.
  exact/min/disjoint_single_of_not_indom.
Qed.

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~(d)~> v) \* H).
Proof using.
  intros. intros s1 K0.
  forwards~ (p&D'&M): (single_fresh s1 v).
  exists (Fmap.union (Fmap.single (p, d) v) s1) (val_loc p). split.
  { applys~ @eval_ref_sep. }
  { applys~ @hstar_intro.
    { exists p. rewrite~ @hstar_hpure_l. split~. { applys~ @hsingle_intro. } } }
Qed.

Lemma hoare_get : forall H v p,
  hoare (val_get p)
    ((p ~(d)~> v) \* H)
    (fun r => \[r = v] \* (p ~(d)~> v) \* H).
Proof using.
  intros. intros s K0. exists s v. split.
  { destruct K0 as (s1&s2&P1&P2&D'&U).
    lets E1: @hsingle_inv P1. subst s1. applys @eval_get_sep U. }
  { rewrite~ @hstar_hpure_l. }
Qed.

Lemma hoare_set : forall H w p v,
  hoare (val_set (val_loc p) v)
    ((p ~(d)~> w) \* H)
    (fun r => \[r = val_unit] \* (p ~(d)~> v) \* H).
Proof using.
  intros. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D'&U).
  lets E1: @hsingle_inv P1.
  exists (Fmap.union (Fmap.single (p, d) v) h2) val_unit. split.
  { subst h1. applys @eval_set_sep U D'. auto. }
  { rewrite hstar_hpure_l. split~.
    { applys~ @hstar_intro.
      { applys~ @hsingle_intro. }
      { subst h1. applys Fmap.disjoint_single_set D'. } } }
Qed.

Lemma hoare_free : forall H p v,
  hoare (val_free (val_loc p))
    ((p ~(d)~> v) \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  intros. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D'&U).
  lets E1: @hsingle_inv P1.
  exists h2 val_unit. split.
  { subst h1. applys eval_free_sep U D'. }
  { rewrite hstar_hpure_l. split~. }
Qed.

(** Other operations. *)

Lemma hoare_unop : forall v H op v1,
  evalunop op v1 v ->
  hoare (op v1)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* @eval1_unop. }
  { rewrite* @hstar_hpure_l. }
Qed.

Lemma hoare_binop : forall v H op v1 v2,
  evalbinop op v1 v2 v ->
  hoare (op v1 v2)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* @eval1_binop. }
  { rewrite* @hstar_hpure_l. }
Qed.

(** Bonus: example of proofs for a specific primitive operation. *)

Lemma hoare_add : forall H (n1 n2 : int),
  hoare (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof.
  dup.
  { intros. applys @hoare_binop. applys @evalbinop_add. }
  { intros. intros s K0. exists s (val_int (n1 + n2)). split.
    { applys @eval1_binop. applys @evalbinop_add. }
    { rewrite* @hstar_hpure_l. } }
Qed.

Lemma hoare_frame H (P : hhprop) Q t fs: 
  hlocal H fs ->
  ~ indom fs d ->
  hoare t P Q -> 
  hoare t (P \* H) (fun v => Q v \* H).
Proof.
  move=> hl ? ht ? [Ph][Hh] [/[dup]?/ht] [h'][v] [ev ?].
  case=> /[dup]/hl lfs ? [disj]->.
  exists (h' \u Hh), v; split*.
  { apply/eval1_frame; eauto. }
  exists h', Hh; splits=> //.
  case: (local_partition_fset Ph (single d tt))=> Phd [Phnd] [fs'][?][?][?][?] E; subst.
  move/eval1_local: ev=> /(_ fs')[] //. 
  { apply/disjoint_inv_not_indom_both; eauto. }
  move=> h'd [lh'] ->.
  move: disj; rewrite ?disjoint_union_eq_l=> -[]; split=> //.
  apply/disjoint_of_not_indom_both=> -[??] /lfs /[swap] /lh'.
  by rewrite indom_single_eq=> <-.
Qed.

End Hoare1.

Lemma local_proj_refl h d (Hl : local (single d tt) h) : proj h d = h.
Proof. 
  apply fmap_extens. intros (p, dd).
  unfold proj, filter. simpl. unfold map_filter.
  destruct (fmap_data h (p, dd)) eqn:E; rewrite E; try reflexivity.
  hnf in Hl. specialize (Hl p dd). rewrite indom_single_eq in Hl.
  case_if; try eqsolve. false Hl. eqsolve.
Qed.

Lemma disjoint_after_proj d h1 h2
  (Hdj : disjoint h1 h2) : disjoint (proj h1 d) (proj h2 d).
Proof.
  apply disjoint_of_not_indom_both. intros (p, dd). rewrite ! filter_indom.
  move=> [H1 <-] [H2 _]. move: H1 H2. by apply disjoint_inv_not_indom_both.
Qed.

Lemma disjoint_of_disj_proj_local d h1 h2 (Hl : local (single d tt) h1)
  (Hdj : disjoint h1 (proj h2 d)) : disjoint h1 h2.
Proof.
  apply disjoint_of_not_indom_both.
  intros (pp, dd) H1 H2.
  apply disjoint_inv_not_indom_both with (x:=(pp, dd)) in Hdj; auto.
  apply Hl in H1. rewrite indom_single_eq in H1. subst.
  by rewrite filter_indom.
Qed.

Lemma eval1_proj_d d h h' t v : 
  eval1 d h t h' v -> 
  eval1 d (proj h d) t (proj h' d) v.
Proof.
  elim; try by (econstructor; eauto).
  { move=> *; rewrite /proj filter_update; [case: classicT=> // _|by case].
    apply/eval1_ref=> >; rewrite filter_indom; autos*. }
  { move=> > ?->; apply/eval1_get; rewrite ?filter_indom // /proj. 
    erewrite <-filter_in; first reflexivity.
    by simpl. }
  { move=> *; rewrite /proj filter_update; [case: classicT=> // _|by case].
    apply/eval1_set=> >; rewrite filter_indom; autos*. }
  { move=> *; rewrite proj_remove_eq.
    apply/eval1_free=> >; rewrite filter_indom; autos*. }
  { introv. intros -> -> Hn Hdj Hlfs.
    rewrite proj_union. apply eval1_alloc with (k:=k).
    2-3: easy.
    { apply local_proj_refl, hconseq_local. }
    { apply disjoint_after_proj; auto. }
    { hnf in Hlfs |- *.
      intros ? ?. apply Hlfs.
      apply disjoint_of_disj_proj_local with (d:=d); auto.
      apply hconseq_local.
    }
  }
  { introv. intros -> -> Hdj.
    rewrite proj_union. eapply eval1_dealloc with (vs:=vs).
    2: reflexivity.
    { rewrite local_proj_refl; auto. apply hconseq_local. }
    { by apply disjoint_after_proj. }
  }
  { introv. intros Hin HH. apply eval1_length.
    { by rewrite filter_indom. }
    { by rewrite filter_in. }
  }
Qed.

Lemma hhoare_update Q' H Q ht fs d :
  ~ Fmap.indom fs d ->
  hoare d (ht d) H Q' -> 
  (forall v, hhoare fs ht (Q' v) (fun hv => Q (upd hv d v))) ->
  hhoare (update fs d tt) ht H Q.
Proof.
  move=> ? HH ?.
  rewrite update_eq_union_single.
  apply/(@hhoare_union _ _ _ _ (fun hv => Q' (hv d))).
  { exact/disjoint_single_of_not_indom. }
  { move=> ? /HH[h'][v][ev ?].
    exists h', (upd (fun (d : D) => v) d v); split*; rewrite ?upd_eq //.
    splits*=> >; rewrite indom_single_eq.
    { move=> <- /[! upd_eq]; exact/eval1_proj_d. }
    apply/eval1_proj_nd; eauto. }
  move=> hv; rewrite update_empty.
  apply/hhoare_conseq; eauto=> ?.
  by rewrite uni_upd ?uni0.
Qed.

Arguments hhoare_update _ {_}.

Lemma hhoareP H Q ht fs : 
  (exists (f : fset D -> (D -> val) -> hhprop),
    (exists hv, f empty hv = H) /\ 
    (forall hv, f fs hv = Q hv) /\
    forall (fs' : fset D) d hv, 
      indom fs d ->
      ~ indom fs' d ->
      hoare d (ht d) (f fs' hv) (fun v => f (update fs' d tt) (upd hv d v))) -> 
        hhoare fs ht H Q.
Proof.
  elim/fset_ind: fs H Q.
  { move=> ??.
    case=> f [][hv <-][/(_ hv)] QE _.
    move=> h /[! QE]. exists h, hv; split*.
    by constructor. }
  move=> fs x IHfs NIND H Q.
  case=> f [][hv<-] [QE] h1.
  apply/(hhoare_update (fun v => f (single x tt) (upd hv x v)))=> //.
  { rewrite update_empty; apply/h1; rewrite // indom_update_eq; eauto. }
  move=> v; apply/(IHfs _ _).
  exists (fun fs hv => f (update fs x tt) (upd hv x v)); splits*.
  { eexists; by rewrite ?update_empty; eauto. }
  move=> fs' d hv'.
  case: (prop_inv (x = d))=> [<- /NIND //|???].
  replace (fun v0 => f (update (update fs' d tt) x tt) (upd (upd hv' d v0) x v)) with 
    (fun v0 => f (update (update fs' x tt) d tt) (upd (upd hv' x v) d v0)).
  { apply/h1; rewrite* indom_update_eq. }
  apply/fun_ext_1=> ?. rewrite update_update 1?upd_upd //.
Qed.

Coercion read : fmap >-> Funclass.

Lemma hlocal_subset fs1 fs2 H :
  (forall x, indom fs1 x -> indom fs2 x) ->
  hlocal H fs1 -> hlocal H fs2.
Proof. by move=> ii hl ? {}/hl hl ?? /hl /ii. Qed.

Arguments hlocal_subset _ {_}.

Lemma hhoare_hstar_fset H (P : D -> hhprop) (Q : D -> val -> hhprop) fs ht :
  (forall d, hlocal (P d) (single d tt)) ->
  (forall d v, hlocal (Q d v) (single d tt)) ->
  (forall d, indom fs d -> 
      hoare d (ht d) (P d \* H) (fun v => Q d v \* H)) ->
  hhoare fs ht ((\*_(d <- fs) P d) \* H) (fun hv => (\*_(d <- fs) Q d (hv d)) \* H).
Proof.
  move=> l l2 h1. 
  apply/hhoareP.
  set f := fun fs' hv => 
    ((\*_(d <- fs \- fs') P d) \* 
    H) \*
    (\*_(d <- fs') Q d (hv d)).
  exists f; splits; rewrite/f.
  { exists (fun (d : D) => arbitrary : val).
    rewrite diff_empty hbig_fset_empty; xsimpl. }
  { move=> ?; rewrite diffxx hbig_fset_empty; xsimpl. }
  move=> fs' d' hv *.
  replace (fun v =>
    ((\*_(d <- fs \- update fs' d' tt) P d) \* H) \*
    \*_(d <- update fs' d' tt) Q d (upd hv d' v d)) with 
    (fun v0 =>
      (((\*_(d <- fs \- update fs' d' tt) P d) \* H) \* Q d' v0) \*
      \*_(d <- fs') Q d (hv d)).
  { eapply hoare_frame; eauto.
    { apply/hlocal_hstar_fset=> x ?.
      apply/(hlocal_subset (single x tt))/l2.
      by move=> ? /[! indom_single_eq]<-. }
    rewrite (diff_upd _ d') // hbig_fset_update //.
    { replace ((P d' \* _) \* H) with 
        ((P d' \* H) \* \*_(d <- fs \- update fs' d' tt) P d) by xsimpl.
      replace (fun v => (_ \* H) \* _) with 
        (fun v => (Q d' v \* H) \* \*_(d <- fs \- update fs' d' tt) P d).
      { apply/hoare_frame; auto.
        apply/hlocal_hstar_fset=> x ?.
        { apply/(hlocal_subset (single x tt))=> // ?.
          rewrite indom_single_eq=><-; eauto. }
        rewrite diff_indom.
        rewrite* indom_update_eq. }
      apply/fun_ext_1. xsimpl. }
    rewrite diff_indom; rewrite* indom_update_eq=> //. }
  apply/fun_ext_1=> v.
  rewrite hbig_fset_update //.
  under (@hbig_fset_eq _ _ _ fs' (fun _ => Q _ (upd _ _ _ _))).
  { move=> ??; rewrite upd_neq; first over.
    by move=> ?; subst. }
  rewrite upd_eq; xsimpl.
Qed.

Ltac hlocal := 
  repeat (intros; 
  match goal with 
  | |- hlocal (_ \* _) _ => apply hlocal_hstar
  | |- hlocal \[] _    => apply hlocal_hempty
  | |- hlocal (hexists _) _ => apply hlocal_hexists
  | |- hlocal (hsingle _ _ _) (single _ _) => apply hlocal_hsingle_single
  | |- hlocal (hpure _) _ => apply hlocal_hpure
  end).

Hint Extern 1 (hlocal _ _) => hlocal.

Lemma hhoare_val_eq H Q fs (f : D -> val) ht :
  hhoare fs ht H (fun hv => \[forall d, indom fs d -> hv d = f d] \* Q) ->
  hhoare fs ht H (fun hv => \[hv = f] \* Q).
Proof.
  move=> hh ? /hh [h'][hv][?][h1][h2][] [E] /hempty_inv-> [?][].
  rewrite union_empty_l=> *.
  exists h2 f; splits*; subst*.
  { by apply/eval_hv; eauto=> ? /E->. }
  exists (empty : hheap D), h2; splits*.
  by exists (@eq_refl _ f).
Qed.

Lemma hhoare_ref' : forall H (f : D -> val) fs,
  hhoare fs (fun d => val_ref (f d))
    H
    (fun hr => (\*_(d <- fs) \exists p, \[hr d = val_loc p] \* p ~(d)~> f d) \* H).
Proof.
  intros.
  replace H with ((\*_(_ <- fs) \[]) \* H) at 1; last by rewrite hbig_fset_emptys //.
  apply (hhoare_hstar_fset _ (fun d v => \exists p, \[v = _] \* _))=> *; autos~.
  replace (\[] \* H) with H by xsimpl.
  exact/hoare_ref.
Qed.

Lemma hstar_fset_hexists {A B} `{Inhab B} (fs : fset A) (Q : B -> A -> hhprop) : 
  (\*_(d <- fs) \exists a, Q a d) = 
  \exists (a : A -> B), \*_(d <- fs) (Q (a d) d).
Proof.
  elim/fset_ind: fs.
  { xsimpl (fun _ : A=> arbitrary : B)=> [|?]; by rewrite ?hbig_fset_empty. }
  move=> fs x IHfs ?; rewrite hbig_fset_update // IHfs; xpull.
  { move=> b f; xsimpl (upd f x b).
    rewrite hbig_fset_update // upd_eq; xsimpl.
    erewrite hbig_fset_eq; first by xsimpl*.
    move=> ??; extens=> ?.
    rewrite upd_neq //; move=> ?; by subst. }
  by move=> f; xsimpl (f x) f; rewrite hbig_fset_update.
Qed.


Lemma hhoare_ref : forall H (f : D -> val) fs,
  hhoare fs (fun d => val_ref (f d))
    H
    (fun hr => (\exists (p : D -> loc), \[hr = val_loc \o p] \* \*_(d <- fs) p d ~(d)~> f d) \* H).
Proof.
  move=> H f fs.
  apply/hhoare_hv/hhoare_conseq; first exact/hhoare_ref'; eauto.
  move=> hr; rewrite hstar_fset_hexists. xpull=> p.
  rewrite hstar_fset_pure_hstar.
  xsimpl (fun x : D => val_loc (p x))=> ?.
  extens=> ?; rewrite /uni; case: classicT; autos*.
Qed.


Lemma hhoare_get : forall H (v : D -> val) (p : D -> loc) fs,
  hhoare fs (fun d => val_get (p d))
    ((\*_(d <- fs) p d ~(d)~> v d) \* H)
    (fun hr => 
      \[hr = v] \* 
      (\*_(d <- fs) p d ~(d)~> v d) \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_assoc -hstar_fset_pure_hstar=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _] \* _)); autos~.
  move=> d ?. 
  apply/hoare_conseq; by [apply hoare_get|eauto|xsimpl].
Qed.

Lemma hhoare_set : forall H (w : D -> val) (v : D -> val) (p : D -> loc) fs,
  hhoare fs (fun d => val_set (val_loc (p d)) (v d))
    ((\*_(d <- fs) p d ~(d)~> w d) \* H)
    (fun hr => \[hr = fun _ => val_unit] \* (\*_(d <- fs) p d ~(d)~> v d) \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_assoc -hstar_fset_pure_hstar=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _] \* _)); autos~.
  move=> d ?. 
  apply/hoare_conseq; by [apply hoare_set|eauto|xsimpl].
Qed.

Lemma hhoare_free : forall H (v : D -> val) (p : D -> loc) fs,
  hhoare fs (fun d => val_free (val_loc (p d)))
    ((\*_(d <- fs) p d ~(d)~> v d) \* H)
    (fun hr => \[hr = fun _ => val_unit] \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_fset_pure=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _])); autos~.
  move=> d ?. 
  apply/hoare_conseq; by [apply hoare_free|eauto|xsimpl].
Qed.

Lemma hhoare_unop : forall (v : D -> val) H (op : D -> prim) (v1 : D -> val) fs,
  (forall d, indom fs d -> evalunop (op d) (v1 d) (v d)) ->
  hhoare fs (fun d => (op d) (v1 d))
    H
    (fun hr => \[hr = v] \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  replace H with ((\*_(_ <- fs) \[]) \* H) at 1; last (rewrite hbig_fset_emptys //).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_fset_pure=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _])); autos~.
  move=> d ?. 
  apply/hoare_conseq; [apply hoare_unop|eauto|xsimpl]; by eauto.
Qed.

Lemma hhoare_binop :  forall (v : D -> val) H (op : D -> prim) (v1 v2 : D -> val) fs,
  (forall d, indom fs d -> evalbinop (op d) (v1 d) (v2 d) (v d)) ->
  hhoare fs (fun d => (op d) (v1 d) (v2 d))
    H
    (fun hr => \[hr = v] \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  replace H with ((\*_(_ <- fs) \[]) \* H) at 1; last (rewrite hbig_fset_emptys //).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_fset_pure=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _])); autos~.
  move=> d ?. 
  apply/hoare_conseq; [apply hoare_binop|eauto|xsimpl]; by eauto.
Qed.

(* ================================================================= *)
(** ** Definition of Separation Logic Triples. *)

(** A Separation Logic triple [triple t H Q] may be defined either in
    terms of Hoare triples, or in terms of [wp], as [H ==> wp t Q].
    We prefer the former route, which we find more elementary. *)
(* 
Definition triple (t : trm) (H : hhprop) (Q:val -> hhprop) : Prop :=
  forall (H' : hhprop), hoare t (H \* H') (Q \*+ H'). *)

Section htriple.

Context (fs : fset D).

Definition htriple (ht : D -> trm) (H : hhprop) (Q : (D -> val) -> hhprop) : Prop :=
  forall (H' : hhprop), hhoare fs ht (H \* H') (Q \*+ H').

Lemma htriple_val_eq H Q (f : D -> val) ht :
  htriple ht H (fun hv => \[forall d, indom fs d -> hv d = f d] \* Q) ->
  htriple ht H (fun hv => \[hv = f] \* Q).
Proof.
  move=> T ?. 
  apply/hhoare_conseq; 
   [ |eauto| move=> ?; rewrite hstar_assoc=> ?; apply:applys_eq_init; reflexivity].
  apply/hhoare_val_eq.
  apply/hhoare_conseq; 
  [ |eauto| move=> ?; rewrite -hstar_assoc=> ?; apply:applys_eq_init; reflexivity].
  exact/T.
Qed.

(** We introduce a handy notation for postconditions of functions
    that return a pointer:  [funloc p => H] is short for
    [fun (r:val) => \exists (p:loc), \[r = val_loc p] \* H)]. *)

Notation "'funloc' p '=>' H" :=
  (fun hr => \exists (p : D -> loc), \[hr = val_loc \o p] \* H)
  (at level 200, p ident, format "'funloc'  p  '=>'  H") : hprop_scope.

(* ================================================================= *)
(** ** Structural Rules *)

(** Consequence and frame rule. *)


Lemma htriple_conseq : forall ht H' Q' H Q,
  htriple ht H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  htriple ht H Q.
Proof using.
  introv M MH MQ. intros HF. applys hhoare_conseq M.
  { xchanges MH. }
  { intros x. xchanges (MQ x). }
Qed.

Lemma htriple_frame : forall ht H Q H',
  htriple ht H Q ->
  htriple ht (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF. applys hhoare_conseq (M (HF \* H')); xsimpl.
Qed.

(** Details for the proof of the frame rule. *)

Lemma htriple_frame' : forall ht H Q H',
  htriple ht H Q ->
  htriple ht (H \* H') (Q \*+ H').
Proof using.
  introv M. unfold htriple in *. rename H' into H1. intros H2.
  applys hhoare_conseq. applys M (H1 \* H2).
  { rewrite hstar_assoc. auto. }
  { intros v. rewrite hstar_assoc. auto. }
Qed.

(** Extraction rules. *)

Lemma htriple_hexists : forall ht (A:Type) (J:A->hhprop) Q,
  (forall x, htriple ht (J x) Q) ->
  htriple ht (hexists J) Q.
Proof using.
  introv M. intros HF. rewrite hstar_hexists.
  applys hhoare_hexists. intros. applys* M.
Qed.

Lemma htriple_hpure : forall ht (P:Prop) H Q,
  (P -> htriple ht H Q) ->
  htriple ht (\[P] \* H) Q.
Proof using.
  introv M. intros HF. rewrite hstar_assoc.
  applys hhoare_hpure. intros. applys* M.
Qed. (* Note: can also be proved from [triple_hexists] *)

Lemma htriple_hforall : forall A (x:A) ht (J:A->hhprop) Q,
  htriple ht (J x) Q ->
  htriple ht (hforall J) Q.
Proof using.
  introv M. applys* @htriple_conseq M. applys @hforall_specialize.
Qed.

Lemma htriple_hwand_hpure_l : forall ht (P:Prop) H Q,
  P ->
  htriple ht H Q ->
  htriple ht (\[P] \-* H) Q.
Proof using.
  introv HP M. applys* @htriple_conseq M. rewrite* @hwand_hpure_l.
Qed.

(** Combined and ramified rules. *)

Lemma htriple_conseq_frame : forall H2 H1 Q1 ht H Q,
  htriple ht H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  htriple ht H Q.
Proof using.
  introv M WH WQ. applys @htriple_conseq WH WQ. applys @htriple_frame M.
Qed.

Lemma htriple_ramified_frame : forall H1 Q1 ht H Q,
  htriple ht H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  htriple ht H Q.
Proof using.
  introv M W. applys @htriple_conseq_frame (Q1 \--* Q) M W.
  { rewrite~ <- @qwand_equiv. }
Qed.

(** Named heaps. *)

Lemma hexists_named_eq : forall H,
  H = (\exists h, \[H h] \* (= h)).
Proof using.
  intros. apply himpl_antisym.
  { intros h K. applys @hexists_intro h.
    rewrite* @hstar_hpure_l. }
  { xpull. intros h K. intros ? ->. auto. }
Qed.

Lemma htriple_named_heap : forall ht H Q,
  (forall h, H h -> htriple ht (= h) Q) ->
  htriple ht H Q.
Proof using.
  introv M. rewrite (hexists_named_eq H).
  applys @htriple_hexists. intros h.
  applys* @htriple_hpure.
Qed.

(* ================================================================= *)
(** ** Rules for Terms *)

Lemma htriple_eval_like : forall ht1 ht2 H Q,
  eval_like fs ht1 ht2 ->
  htriple ht1 H Q ->
  htriple ht2 H Q.
Proof using.
  introv E M1. intros H'. applys @hhoare_eval_like E. applys M1.
Qed.

Lemma htriple_val : forall (v : D -> val) H Q,
  H ==> Q v ->
  htriple (fun d => trm_val (v d)) H Q.
Proof using.
  introv M. intros HF. applys @hhoare_val. { xchanges M. }
Qed.

Lemma htriple_fun : forall (x : D -> var) ht1 H Q,
  H ==> Q (fun d => val_fun (x d) (ht1 d)) ->
  htriple (fun d => trm_fun (x d) (ht1 d)) H Q.
Proof using.
  introv M. intros HF. applys~ @hhoare_fun. { xchanges M. }
Qed.

Lemma htriple_fix : forall (f x : D -> var) ht1 H Q,
  H ==> Q (fun d => val_fix (f d) (x d) (ht1 d)) ->
  htriple (fun d => trm_fix (f d) (x d) (ht1 d)) H Q.
Proof using.
  introv M. intros HF. applys~ @hhoare_fix. { xchanges M. }
Qed.

Lemma htriple_seq : forall ht1 ht2 H Q H1,
  htriple ht1 H (fun hv => H1) ->
  htriple ht2 H1 Q ->
  htriple (fun d => trm_seq (ht1 d) (ht2 d)) H Q.
Proof using.
  introv M1 M2. intros HF. applys hhoare_seq.
  { applys M1. }
  { applys hhoare_conseq M2; xsimpl. }
Qed.

Lemma htriple_let : forall x t1 t2 Q1 H Q,
  htriple t1 H Q1 ->
  (forall v1, htriple (fun d => subst (x d) (v1 d) (t2 d)) (Q1 v1) Q) ->
  htriple (fun d => trm_let (x d) (t1 d) (t2 d)) H Q.
Proof using.
  introv M1 M2. intros HF. applys hhoare_let.
  { applys M1. }
  { intros v. applys hhoare_conseq M2; xsimpl. }
Qed.

Lemma htriple_let_val : forall x v1 t2 H Q,
  htriple (fun d => subst (x d) (v1 d) (t2 d)) H Q ->
  htriple (fun d => trm_let (x d) (v1 d) (t2 d)) H Q.
Proof using.
  introv M. applys htriple_let (fun v => \[v = v1] \* H).
  { applys htriple_val. xsimpl*. }
  { intros v. applys htriple_hpure. intros ->. applys M. }
Qed.

Lemma htriple_if : forall (b:D -> bool) t1 t2 H Q,
  htriple (fun d => if (b d) then (t1 d) else (t2 d)) H Q ->
  htriple (fun d => trm_if (b d) (t1 d) (t2 d)) H Q.
Proof using.
  introv M1. intros HF. applys hhoare_if. applys M1.
Qed.

Lemma htriple_app_fun : forall x v1 v2 t1 H Q,
  (forall d, indom fs d -> v1 d = val_fun (x d) (t1 d)) ->
  htriple (fun d => subst (x d) (v2 d) (t1 d)) H Q ->
  htriple (fun d => trm_app (v1 d) (v2 d)) H Q.
Proof using.
  (* can also be proved using [triple_eval_like] *)
  unfold htriple. introv E M1. intros H'.
  applys hhoare_app_fun E. applys M1.
Qed.

Lemma htriple_app_fun_direct : forall x v2 t1 H Q,
  htriple (fun d => subst (x d) (v2 d) (t1 d)) H Q ->
  htriple (fun d => trm_app (val_fun (x d) (t1 d)) (v2 d)) H Q.
Proof using. introv M. applys* htriple_app_fun. Qed.

Lemma htriple_app_fix : forall v1 v2 f x t1 H Q,
  (forall d, indom fs d -> v1 d = val_fix (f d) (x d) (t1 d)) ->
  htriple (fun d => subst (x d) (v2 d) (subst (f d) (v1 d) (t1 d))) H Q ->
  htriple (fun d => trm_app (v1 d) (v2 d)) H Q.
Proof using.
  (* can also be proved using [htriple_eval_like] *)
  unfold htriple. introv E M1. intros H'.
  applys hhoare_app_fix E. applys M1.
Qed.

Lemma htriple_app_fix_direct : forall v2 f x t1 H Q,
  htriple (fun d => subst x v2 (subst f (val_fix f x t1) t1)) H Q ->
  htriple (fun d => trm_app (val_fix f x t1) v2) H Q.
Proof using. introv M. applys* htriple_app_fix. Qed.

(* ================================================================= *)
(** ** Triple-Style Specification for Primitive Functions *)

(** Operations on the state. *)

Lemma htriple_ref : forall (v : D -> val),
  htriple (fun d => val_ref (v d))
    \[]
    (funloc p => \*_(d <- fs) p d ~(d)~> v d).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_ref; xsimpl~.
Qed.

Lemma htriple_get : forall v (p : D -> loc),
  htriple (fun d => val_get (p d))
    (\*_(d <- fs) p d ~(d)~> v d)
    (fun hr => \[hr = v] \* (\*_(d <- fs) p d ~(d)~> v d)).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_get; xsimpl~.
Qed.

Lemma htriple_set : forall (w : D -> val) (p : D -> loc) (v : D -> val),
  htriple (fun d => val_set (val_loc (p d)) (v d))
    (\*_(d <- fs) p d ~(d)~> w d)
    (fun _ => \*_(d <- fs) p d ~(d)~> v d).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_set; xsimpl~.
Qed.

Lemma htriple_free : forall (p : D -> loc) v,
  htriple (fun d => val_free (val_loc (p d)))
    (\*_(d <- fs) p d ~(d)~> v d)
    (fun _ => \[]).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_free; xsimpl~.
Qed.

(** Other operations. *)

Lemma htriple_unop : forall v op v1,
  (forall d, indom fs d -> evalunop (op d) (v1 d) (v d)) ->
  htriple (fun d => (op d) (v1 d)) \[] (fun hr => \[hr = v]).
Proof using.
  introv R. unfold htriple. intros H'.
  applys* hhoare_conseq hhoare_unop. xsimpl*.
Qed.

Lemma htriple_binop : forall v (op : D -> prim) v1 v2,
  (forall d, indom fs d -> evalbinop (op d) (v1 d) (v2 d) (v d)) ->
  htriple (fun d => (op d) (v1 d) (v2 d)) \[] (fun hr => \[hr = v]).
Proof using.
  introv R. unfold htriple. intros H'.
  applys* hhoare_conseq hhoare_binop. xsimpl*.
Qed.


Lemma htriple_add : forall (n1 n2 : D -> int),
  htriple (fun d => val_add (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (n1 d + n2 d)]).
Proof using. intros. applys* htriple_binop; intros. apply evalbinop_add. Qed.

Lemma htriple_float_add : forall (f1 f2 : D -> binary64),
  htriple (fun d => val_float_add (f1 d) (f2 d))
    \[]
    (fun hr => \[hr = fun d => val_float (f1 d + f2 d)%F64]).
Proof using. intros. applys* htriple_binop; intros. apply evalbinop_float_add. Qed.

Lemma htriple_div : forall (n1 n2 : D -> int),
  (forall d, indom fs d -> n2 d <> 0) ->
  htriple (fun d => val_div (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (Z.quot (n1 d) (n2 d))]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_div. Qed.

Lemma htriple_neg : forall (b1:D -> bool),
  htriple (fun d => val_neg (b1 d))
    \[]
    (fun hr => \[hr = fun d => val_bool (LibBool.neg (b1 d))]).
Proof using. intros. applys* htriple_unop; intros; applys* evalunop_neg. Qed.

Lemma htriple_opp : forall (n1 : D -> int),
  htriple (fun d => val_opp (n1 d))
    \[]
    (fun hr => \[hr = fun d => val_int (- (n1 d))]).
Proof using. intros. applys* htriple_unop; intros; applys* evalunop_opp. Qed.

Lemma htriple_eq : forall (v1 v2 : D -> val),
  htriple (fun d => val_eq (v1 d) (v2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue ((v1 d) = (v2 d))]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_eq. Qed.

Lemma htriple_neq : forall (v1 v2 : D -> val),
  htriple (fun d => val_neq (v1 d) (v2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (v1 d <> v2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys evalbinop_neq. Qed.

Lemma htriple_sub : forall (n1 n2 : D -> int),
  htriple (fun d => val_sub (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (n1 d - n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_sub. Qed.

Lemma htriple_mul : forall (n1 n2 : D -> int),
  htriple (fun d => val_mul (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (n1 d * n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_mul. Qed.

Lemma htriple_float_mkpair : forall (f1 f2 : D -> binary64),
  htriple (fun d => val_float_mkpair (f1 d) (f2 d))
    \[]
    (fun hr => \[hr = fun d => val_floatpair (f1 d) (f2 d)]).
Proof using. intros. applys* htriple_binop; intros. apply evalbinop_float_mkpair. Qed.

Lemma htriple_float_fma : forall (f1 f2 f3 : D -> binary64),
  htriple (fun d => val_float_fma (val_floatpair (f1 d) (f2 d)) (f3 d))
    \[]
    (fun hr => \[hr = fun d => val_float (@BFMA _ Tdouble (f1 d) (f2 d) (f3 d))]).
Proof using. intros. applys* htriple_binop; intros. apply evalbinop_float_fma. Qed.

Lemma htriple_mod : forall (n1 n2 : D -> int),
  (forall d, indom fs d -> n2 d <> 0) ->
  htriple (fun d => val_mod (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (Z.rem (n1 d) (n2 d))]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_mod. Qed.

Lemma htriple_le : forall (n1 n2 : D -> int),
  htriple (fun d => val_le (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (n1 d <= n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_le. Qed.

Lemma htriple_lt : forall (n1 n2 : D -> int),
  htriple (fun d => val_lt (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (n1 d < n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_lt. Qed.

Lemma htriple_ge : forall (n1 n2 : D -> int),
  htriple (fun d => val_ge (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (n1 d >= n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_ge. Qed.

Lemma htriple_gt : forall (n1 n2 : D -> int),
  htriple (fun d => val_gt (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (n1 d > n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_gt. Qed.

Lemma htriple_ptr_add : forall (p : D -> loc) (n : D -> int),
  (forall d, indom fs d -> p d + n d >= 0) ->
  htriple (fun d => val_ptr_add (p d) (n d))
    \[]
    (fun hr => \[hr = fun d => val_loc (abs (p d + n d))]).
Proof using.
  intros. applys* htriple_binop; intros; applys* evalbinop_ptr_add.
  { rewrite~ abs_nonneg. }
Qed.

Lemma htriple_ptr_add_nat : forall (p : D -> loc) (f:D -> nat),
  htriple (fun d => val_ptr_add (p d) (f d))
    \[]
    (fun hr => \[hr = fun d => val_loc (p d + f d)%nat]).
Proof using.
  intros. applys htriple_conseq htriple_ptr_add. { lia. } { xsimpl. }
  { xsimpl. intros. subst. 
    applys fun_ext_1; intros; fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; lia. }
Qed.

(* ================================================================= *)
(** ** Alternative Definition of [wp] *)

(* ----------------------------------------------------------------- *)
(** *** Definition of the Weakest-Precondition Judgment. *)

(** [wp] is defined on top of [hhoare] htriples. More precisely [wp t Q]
    is a heap predicate such that [H ==> wp t Q] if and only if
    [htriple t H Q], where [htriple t H Q] is defined as
    [forall H', hhoare t (H \* H') (Q \*+ H')]. *)

Definition wp t := fun Q =>
  \exists H, H \* \[forall H', hhoare fs t (H \* H') (Q \*+ H')].

(** Equivalence with htriples. *)

Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (htriple t H Q).
Proof using.
  unfold wp, htriple. iff M.
  { intros H'. applys hhoare_conseq. 2:{ applys @himpl_frame_l M. }
      { clear M. rewrite hstar_hexists. applys hhoare_hexists. intros H''.
        rewrite (hstar_comm H''). rewrite hstar_assoc.
        applys hhoare_hpure. intros N. applys N. }
      { auto. } }
  { xsimpl H. apply M. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Structural Rule for [wp] *)

(** The ramified frame rule. *)

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using.
  intros. unfold wp. xpull. intros H M.
  xsimpl (H \* (Q1 \--* Q2)). intros H'.
  applys hhoare_conseq M; xsimpl.
Qed.

Arguments wp_ramified : clear implicits.

(** Corollaries. *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  introv M. applys @himpl_trans_r (wp_ramified Q1 Q2). xsimpl. xchanges M.
Qed.

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using. intros. applys @himpl_trans_r wp_ramified. xsimpl. Qed.

Lemma wp_ramified_frame : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys @himpl_trans_r wp_ramified. xsimpl. Qed.

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.


(* ----------------------------------------------------------------- *)
(** *** Weakest-Precondition Style Reasoning Rules for Terms. *)

Lemma wp_eval_like : forall t1 t2 Q,
  eval_like fs t1 t2 ->
  wp t1 Q ==> wp t2 Q.
Proof using.
  introv E. unfold wp. xpull. intros H M. xsimpl H.
  intros H'. applys hhoare_eval_like E M.
Qed.

Lemma wp_val : forall v Q,
  Q v ==> wp (fun d => trm_val (v d)) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hhoare_val. xsimpl. Qed.

Lemma wp_fun : forall x t Q,
  Q (fun d => val_fun (x d) (t d)) ==> wp (fun d => trm_fun (x d) (t d)) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hhoare_fun. xsimpl. Qed.

Lemma wp_fix : forall f x t Q,
  Q (fun d => val_fix (f d) (x d) (t d)) ==> wp (fun d => trm_fix (f d) (x d) (t d)) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hhoare_fix. xsimpl. Qed.

Lemma wp_fix_app2 : forall f x t Q (v : val),
  wp (fun d => trm_fix (f d) (x d) (t d) v) Q = wp (fun d => val_fix (f d) (x d) (t d) v) Q.
Proof using. intros. unfold wp. xsimpl;intros H' ??; applys* hhoare_fix_app2. Qed.

Lemma wp_fix_app2' : forall f x t Q (v : _ -> val),
  wp (fun d => trm_fix (f d) (x d) (t d) (v d)) Q = wp (fun d => val_fix (f d) (x d) (t d) (v d)) Q.
Proof using. intros. unfold wp. xsimpl;intros H' ??; applys* hhoare_fix_app2'. Qed.

Lemma wp_fix_appapp2 : forall f x t t' Q (v : val),
  wp (fun d => trm_seq t' (trm_fix (f d) (x d) (t d) v)) Q = wp (fun d => trm_seq t' (val_fix (f d) (x d) (t d) v)) Q.
Proof using. intros. unfold wp. xsimpl;intros H' ??; applys* hhoare_fix_appapp2. Qed.

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  (forall d, v1 d = val_fun (x d) (t1 d)) ->
  wp (fun d => subst (x d) (v2 d) (t1 d)) Q ==> wp (fun d => trm_app (v1 d) (v2 d)) Q.
Proof using. introv EQ1. unfold wp. xsimpl; intros. applys* hhoare_app_fun. Qed.
(* variant: introv EQ1. applys wp_eval_like. introv R. applys* eval_app_fun. *)

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  (forall d, v1 d = val_fix (f d) (x d) (t1 d)) ->
  wp (fun d => subst (x d) (v2 d) (subst (f d) (v1 d) (t1 d))) Q ==> wp (fun d => trm_app (v1 d) (v2 d)) Q.
Proof using. introv EQ1. unfold wp. xsimpl; intros. applys* hhoare_app_fix. Qed.
(* variant: introv EQ1. applys wp_eval_like. introv R. applys* eval_app_fix. *)

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun hr => wp t2 Q) ==> wp (fun d => trm_seq (t1 d) (t2 d)) Q.
Proof using.
  intros. unfold wp at 1. xsimpl. intros H' M1.
  unfold wp at 1. xsimpl. intros H''.
  applys hhoare_seq. applys (rm M1). applys* wp_equiv.
Qed.

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (fun d => subst (x d) (v d) (t2 d)) Q) ==> wp (fun d => trm_let (x d) (t1 d) (t2 d)) Q.
Proof using.
  intros. unfold wp at 1. xsimpl. intros H' M1.
  unfold wp at 1. xsimpl. intros H''.
  applys hhoare_let. applys (rm M1). intros v. simpl. unfold wp.
  repeat rewrite hstar_hexists. applys hhoare_hexists; intros H'''.
  rewrite (hstar_comm H'''). rewrite hstar_assoc.
  applys hhoare_hpure; intros M2. applys hhoare_conseq M2; xsimpl.
Qed.

Lemma wp_if : forall (b : D -> bool) t1 t2 Q,
  wp (fun d => if (b d) then (t1 d) else (t2 d)) Q ==> wp (fun d => trm_if (b d) (t1 d) (t2 d)) Q.
Proof using.
  intros. repeat unfold wp. xsimpl; intros H M H'.
  applys hhoare_if. applys M.
Qed.

Lemma wp_if_case : forall b t1 t2 Q,
  (if b then wp t1 Q else wp t2 Q) ==> wp (fun d => trm_if b (t1 d) (t2 d)) Q.
Proof using. intros. applys @himpl_trans wp_if. case_if~. Qed.

Lemma wp_ht_eq ht1 ht2 Q : 
  (forall d, indom fs d -> ht1 d = ht2 d) ->
  wp ht1 Q = wp ht2 Q.
Proof.
  by move=> E; rewrite /wp; xsimpl=> ? /[swap] H'/(_ H') /hhoare_eq; apply=> ? /E->.
Qed.

Lemma wp_hv ht Q :
  wp ht (fun hv => \exists hv', Q (hv \u_(fs) hv')) ==>
  wp ht Q.
Proof.
  rewrite /wp. xsimpl=> H' hh ?.
  apply/hhoare_hv/hhoare_conseq; eauto.
  by xsimpl.
Qed.

End htriple.

Lemma htriple_proj (fs fs' : fset D) H H' (Q Q' : _ -> hhprop) ht : 
  disjoint fs fs' -> 
  hlocal H fs -> (forall hv, hlocal (Q hv) fs) -> 
  hlocal H' fs' -> (forall hv, hlocal (Q' hv) fs') -> 
  (exists h, H' h) ->
  htriple (fs \u fs') ht (H \* H') (fun hv => Q hv \* Q' hv) ->
  htriple fs ht H Q.
Proof.
  move=> dj ????? hh.
  apply/baz=> h ?.
  apply/hhoare_proj; eauto.
  { by apply/hlocal_hstar=> // ?->. }
  { by move=> ?; apply/hlocal_hstar=> // ?->. }
  apply/hhoare_conseq. apply/(hh (= h)). all: xsimpl*.
Qed.

Lemma htriple_proj' (fs fs' : fset D) H H' (Q Q' : _ -> hhprop) ht : 
  disjoint fs fs' -> 
  hlocal H fs -> (forall hv, hlocal (Q hv) fs) -> 
  hlocal H' fs' -> (forall hv, hlocal (Q' hv) fs') -> 
  (forall h, H h -> exists h', H' h') ->
  htriple (fs \u fs') ht (H \* H') (fun hv => Q hv \* Q' hv) ->
  htriple fs ht H Q.
Proof.
  move=> dj ????? hh.
  apply/baz=> h ?.
  apply/hhoare_proj'; eauto.
  { by apply/hlocal_hstar=> // ?->. }
  { by move=> ?; apply/hlocal_hstar=> // ?->. }
  { intros ? Hh0. apply hstar_inv in Hh0. destruct Hh0 as (h1 & ? & Hh1 & <- & Hdj & ->).
    eauto. }
  apply/hhoare_conseq. apply/(hh (= h)). all: xsimpl*.
Qed.

Lemma fsubst_update_valid' {A B C : Type} (f : A -> C) (fm : fmap A B) x y: 
  valid_subst' (update fm x y) f ->
  valid_subst' fm f ->
  fsubst (update fm x y) f = update (fsubst fm f) (f x) y.
Proof.
  move=> v v'. apply/fmap_extens=> z.
  rewrite {2}/update /union {2}/fmap_data /map_union /single {2}/fmap_data.
  case: classicT=> [<-|?].
  { rewrite /fsubst {1}/fmap_data /map_fsubst.
    case: classicT=> [pf|].
    { case: (indefinite_description _).
      move=> {}z []/v/[apply]->; last by (rewrite indom_update_eq; left).
      rewrite /= /map_union; by case: classicT. }
    case; exists x; split=> //.
    exact/indom_update. }
  rewrite /map_fsubst /map_union.
  rewrite {1}/fsubst {1}/fmap_data /map_fsubst; case: classicT=>[pf|].
  { case: (indefinite_description _)=> w[]?; subst=> ?.
    have: (indom (update fm x y) w) by [].
    rewrite indom_update_eq=> -[?|?]; first by subst.
    rewrite /= /map_union; case: classicT=> [?|?]; first by subst.
    rewrite /map_fsubst; case: classicT=> [?|].
    { by case: (indefinite_description _)=> ?[]/v'/[apply]->. }
    case; by exists w. }
  move=> pf /=; rewrite /map_fsubst; case: classicT=> //.
  move=> ?; case: (indefinite_description _)=> w[]??; subst.
  case: pf; exists w; split=> //.
  suff: indom (update fm x y) w by [].
  rewrite indom_update_eq; by right.
Qed. 

Lemma valid_subst_union {A B C : Type} (fm1 fm2 : fmap A B) (f : A -> C) :
  valid_subst fm1 f ->
  valid_subst fm2 f ->
  valid_subst (fm1 \u fm2) f.
Proof.
  move=> v1 v2 x1 x2 /[dup]/v1/[swap]/v2.
  rewrite /union/map_union /= => ->->.
  by case: (fmap_data _ _).
Qed.

Lemma exists_valid h (f : D -> D) (fs : fset D) : 
  (forall d d', d <> d' -> f d = f d' -> indom fs d /\ indom fs d') ->
  local fs h ->
  valid_subst' h (fun x => (x.1, f x.2)) ->
  exists (h' : hheap D), 
    valid_subst h' (fun x => (x.1, f x.2)) /\ 
    local fs h' /\
    fsubst h' (fun x => (x.1, f x.2)) = 
    fsubst h (fun x => (x.1, f x.2)).
Proof.
  move=> fP.
  elim/fmap_ind: h.
  { by exists (empty : hheap D). }
  move=> h [l d] x IHh ndm lc v.
  have?: valid_subst' h (fun x0 : loc * D => (x0.1, f x0.2)).
  { move=> ??++ /v /=; move: ndm; rewrite /map_union.
    rewrite ?indom_update_eq; case: classicT=> [<-|] //.
    by case: classicT=> [<-|] // ?????; apply; right. }
  have[??]: (indom fs d /\ local fs h).
  { split.
    { apply/lc; rewrite indom_update_eq; left; eauto. }
    move=> > ind; apply/lc;rewrite indom_update_eq; right; eauto. }
  case: IHh=> // h'[v'][lc' fE].
  set (fs' := filter (fun x _ => f d = f x) fs).
  set (hd := Union fs' (fun d' => single (l, d') x)).
  have hdE: (forall l' d', 
    fmap_data hd (l', d') = 
      If (l' = l /\ f d = f d') then Some x else None).
  { move=> ? d'; case: classicT=> [[-> ffE]|]; rewrite /hd /fs'.
    { rewrite (Union_fmap_indomE d').
      { by move=> /=; do ? case:classicT. }
      { by move=> *; apply disjoint_single_single=> -[]. }
      { rewrite filter_indom; split*.
        by case: (prop_inv (d = d'))=> [<-//|] /fP []. }
      by rewrite indom_single_eq. }
    move=> F. rewrite ?Union_fmap_nindomE // => >.
    rewrite filter_indom indom_single_eq=> -[]??[]??. subst.
    autos*. }
  have?: valid_subst hd (fun x : hloc D => (x.1, f x.2)).
  { by case=> ? d' [l' d''] /=[->] /[! hdE]->. }
  have?: valid_subst (hd \u h') (fun x : hloc D => (x.1, f x.2)).
  { exact/valid_subst_union. }
  have ind: (forall x, indom hd x = (f x.2 = f d /\ x.1 = l)).
  { case=> l' d' /=; rewrite /indom /map_indom.
    by rewrite hdE; case: classicT; extens; splits*. }
  exists (hd \u h'); splits*.
  { rewrite /local=>? d'; rewrite indom_union_eq=> -[|/lc']//.
    rewrite ind /= => -[].
    by case: (prop_inv (d' = d))=> [->|]// /fP/[apply]-[]. }
  rewrite fsubst_union_valid // fsubst_update_valid' // fE.
  congr union=> /=.
  rewrite /indom in ind.
  apply/fmap_extens=> -[??]; rewrite /= /map_fsubst.
  case: classicT=> [pf|].
  { case: (indefinite_description _); clear pf=> -[]/=? d' [][->]<-/[! ind]/=.
    rewrite hdE=> -[->->]; case: classicT=> [|[]//].
    by case: classicT. }
  case: classicT=> //-[<-]<- []; exists (l, d); split*.
  by rewrite ind.
Qed.

Lemma fsubst_cancel' {A B C : Type} (fm : fmap A B) (g : A -> C) f : 
  (forall x, indom fm x -> f (g x) = x) -> 
  fsubst (fsubst fm g) f = fm.
Proof.
  move=> c.
  have v: (valid_subst' fm g).
  { by move=> ??/=??/(congr1 f)/[! c] // ->. }
  apply/fmap_extens=> x.
  rewrite {1}/fsubst {1}/fmap_data /map_fsubst; case: classicT=> [pf|].
  { case: (indefinite_description _); clear pf.
    move=> y [<-]. move: (fsubst_valid_indom g fm y).
    rewrite /indom=> -> [?][<-] ? /[! c] //=.
    rewrite /map_fsubst; case: classicT=> [pf|[] ].
    { case: (indefinite_description _)=> ?[]/[swap]?/(congr1 f).
      by rewrite ?c // => ->. }
    eexists; eauto. }
  case: (prop_inv (indom fm x))=> [ind[]|/not_not_inv->//].
  exists (g x); split=> //; first by rewrite c.
  move: (fsubst_valid_indom g fm); rewrite /indom /==> ->; by eexists.
Qed.


Lemma exists_valid_hsub h (f : D -> D) (fs : fset D) g :
  local (fsubst fs f) h ->
  (forall x, indom (fsubst fs f) x -> f (g x) = x) ->
  (forall x, indom (fsubst fs f) x <-> indom fs (g x)) ->
  (forall d d', d <> d' -> f d = f d' -> indom fs d /\ indom fs d') ->
  exists (h' : hheap D), 
    valid_subst h' (fun x => (x.1, f x.2)) /\
    local fs h' /\
    (= h) = hsub (= h') f.
Proof.
  move=> lc c dmE /[dup] fP. 
  have ?: (valid_subst h (fun x => (x.1, g x.2))).
  { case=> ? d1 [? d2]/=[->]/[dup]gE/(congr1 f). 
    case: (prop_inv (indom fs (g d1)))=> /[dup]; rewrite {1}gE.
    { by rewrite -?dmE=> ?? /[! c] // ->. }
    by move=> ?? _; rewrite ?fmapNone // => /lc /[! dmE]. }
  case/(@exists_valid (fsubst h (fun x => (x.1, g x.2)))).
  { move=> ??.
    rewrite fsubst_valid_indom=> -[][??][]/=[]_<-/lc.
    by rewrite dmE. }
  { case=> ??[??]. rewrite ?fsubst_valid_indom //.
    case=> -[? d1] /=[][_<-]_[][? d2]/=[][_<-]_[->]/[dup]fE.
    case: (prop_inv (g d1 = g d2))=> [->|]// /fP/[apply]-[].
    by rewrite -?dmE=> ??; move: fE; rewrite ?c // => ->.  }
  move=> h' [v'] /[! @fsubst_cancel'][[? E]|[??] /=].
  { exists h'; splits=>//; extens=> h''; split=> [->|].
    { exists h'; splits*. }
    by case=> ? []/[swap]-[]/[swap]-> /[! E] _->. }
  by move=> /lc ? /[! c].
Qed.

Lemma valid_subst_union_l {A B C : Type} (fm1 fm2 : fmap A B) (f : A -> C) :
  valid_subst fm1 f ->
  disjoint fm1 fm2 ->
  valid_subst (fm1 \u fm2) f ->
    valid_subst fm2 f.
Proof.
  move=> v1 dj v12 x1 x2 /[dup]/[dup] /v12/[swap]/v1.
  rewrite /union /= /map_union=> /[dup]+->.
  case: (dj x2)=> [->|] // .
  by case: (dj x1)=> [->?<-|-> ->].
Qed.

Lemma valid_subst_disj {A B C : Type} (fm1 fm2 : fmap A B) (f : A -> C) :
  disjoint fm1 fm2 ->
  valid_subst fm1 f ->
  valid_subst fm2 f ->
    disjoint (fsubst fm1 f) (fsubst fm2 f).
Proof.
  move=> c v1 v2 x.
  case: (prop_inv (exists y, f y = x))=> [[?<-]|].
  { by rewrite ?fsubst_valid_eq. }
  move=> F; rewrite fmapNone; first by left.
  rewrite fsubst_valid_indom=>-[?][]*; apply/F.
  exists; eauto.
Qed.


Arguments valid_subst_disj {_ _ _ _ _} _.

Lemma hsub_hstar_l h Q (f : D -> D) g (fs : fset D): 
  (* local (fsubst fs f) h -> *)
  (forall x, indom (fsubst fs f) x -> f (g x) = x) ->
  valid_subst h (fun x => (x.1, f x.2)) ->
  hsub ((= h) \* Q) f = 
  hsub (= h) f \* hsub Q f.
Proof.
  move=>  c v.
  extens=> s; split.
  { case=> h' [<-][v'][h1][h2][?][?][dj]?; subst.
    exists 
      (fsubst h (fun x => (x.1, f x.2))),
      (fsubst h2 (fun x => (x.1, f x.2))).
    have?: valid_subst h2 (fun x : loc * D => (x.1, f x.2)).
    { exact/valid_subst_union_l/v'. }
    splits.
    { exists h; splits*. }
    { exists h2; splits*. }
    { apply (valid_subst_disj (fun x : loc * D => (x.1, f x.2)) dj) => // -[]/=*. }
    by rewrite fsubst_union_valid. }
  case=> ?[?][] [?][<-][]/[swap]-> _[] [h1][<-][v1]? [dj]->.
  have?: valid_subst (h \u h1) (fun x : loc * D => (x.1, f x.2)).
  { exact/valid_subst_union. }
  exists (h \u h1); splits*.
  { by rewrite fsubst_union_valid. }
  exists h, h1; splits=>//.
  by apply/valid_subst_disj_inv=> //.
Qed.

Lemma hsub_hstar_r h Q f g (fs : fset D): 
  (* local (fsubst fs f) h -> *)
  (forall x, indom (fsubst fs f) x -> f (g x) = x) ->
  valid_subst h (fun x => (x.1, f x.2)) ->
  hsub (Q \* (= h)) f = 
  hsub Q f \* hsub (= h) f.
Proof. by move=>  c ?; rewrite hstar_comm (hsub_hstar_l _ _ c) // hstar_comm. Qed.

Arguments hhoare_hsub {_ _ _} _.

Lemma htriple_hsub (fs : fset D) ht H Q f g : 
  (forall x, indom (fsubst fs f) x -> f (g x) = x) ->
  (forall hv hv', (forall x, indom fs x -> hv x = hv' x) -> Q hv = Q hv') ->
  (forall d d', d <> d' -> f d = f d' -> indom fs d /\ indom fs d') ->
  (forall x, indom (fsubst fs f) x <-> indom fs (g x)) ->
  htriple fs (ht \o f) H Q ->
  htriple (fsubst fs f) ht (hsub H f) (fun hv => hsub (Q (hv \o f)) f).
Proof.
  move=> c QP fP gP hh. 
  apply/baz=> h lc.
  case: (exists_valid_hsub _ lc c gP fP)=> h' [?][lc'->].
  rewrite -(hsub_hstar_r _ _ c)//.
  replace (fun x : D -> val => hsub (Q (x \o f)) f \* hsub (eq^~ h') f) with 
  (fun x : D -> val => hsub (Q (x \o f) \* eq^~ h') f).
  { apply/(hhoare_hsub (fun hv => Q hv \* _))=> // hv //.
    { exact/c. }
    by move=> *; erewrite QP. }
  by extens=> >; rewrite (hsub_hstar_r _ _ c).
Qed.

Lemma valid_subst_id_local (fs : fset D) h f : 
  (forall x, indom fs x -> f x = x) ->
  (forall d d', d <> d' -> f d = f d' -> ~ indom fs d /\ ~ indom fs d') ->
  local fs h ->
    valid_subst h (fun x : loc * D => (x.1, f x.2)).
Proof.
  move=> fid fP lc [? d][? d']/=[->].
  case: (prop_inv (d = d'))=> [->|] // /fP/[apply]-[??].
  by rewrite ?fmapNone=> // /lc.
Qed.

Lemma fsubst_id_local (fs : fset D) h f : 
  (forall x, indom fs x -> f x = x) ->
  (forall d d', d <> d' -> f d = f d' -> ~ indom fs d /\ ~ indom fs d') ->
  local fs h ->
    fsubst h (fun x : loc * D => (x.1, f x.2)) = h.
Proof.
  move=> fid fP lc.
  apply/fmap_extens=> -[l d].
  case: (prop_inv (indom fs d))=> [|nd].
  { move=> /fid{1}<-. rewrite (fsubst_valid_eq (l, d)) //.
    apply/valid_subst_id_local; eauto. }
  rewrite ?fmapNone // => [/lc|] //.
  by rewrite fsubst_valid_indom=> -[][??]/=[][->] fE/[dup]/lc/fid<-/[!fE]/lc.
Qed.

Lemma hsub_idE (fs : fset D) (h : hheap D) f : 
  (forall x, indom fs x -> f x = x) ->
  (forall d d', d <> d' -> f d = f d' -> ~ indom fs d /\ ~ indom fs d') ->
  local fs h ->
    hsub (= h) f = (= h).
Proof.
  move=> ???; extens=> ?; split=> [|->].
  { case=> ? []/[swap]-[]?->.
    by rewrite* (@fsubst_id_local fs). }
  exists h; splits*.
  { applys* fsubst_id_local. }
  applys* valid_subst_id_local.
Qed.


Lemma hsub_hstar_id_eq_l (fs : fset D) h Q f :
  (forall x, indom fs x -> f x = x) ->
  (forall d d', d <> d' -> f d = f d' -> ~ indom fs d /\ ~ indom fs d') ->
  local fs h ->
    hsub ((= h) \* Q) f = (= h) \* hsub Q f.
Proof.
  move=> fid fP lc.
  rewrite (hsub_hstar_l _ id (fs := fs)) ?(@hsub_idE fs) //.
  { by move=> ?; rewrite indom_fsubst=> -[?][]<-/fid{1}->. }
  applys* valid_subst_id_local.
Qed.

Lemma hsub_hstar_id_l (fs : fset D) H Q f :
  (forall x, indom fs x -> f x = x) ->
  (forall d d', d <> d' -> f d = f d' -> ~ indom fs d /\ ~ indom fs d') ->
  hlocal H fs ->
    hsub (H \* Q) f = H \* hsub Q f.
Proof.
  move=> ?? lh; extens=> h; split.
  { case=> h'[?] [?][h1][h2][*].
    have: hsub ((= h1) \* Q) f h.
    { exists h'; splits*; exists h1, h2; splits*. }
    rewrite (@hsub_hstar_id_eq_l fs) //; last exact/lh.
    move: (h); rewrite -/(himpl _ _). 
    by xsimpl=> ? ->. }
  case=> h1 [h2][*].
  have: ((= h1) \* hsub Q f) h by exists h1, h2; splits*.
  rewrite -(@hsub_hstar_id_eq_l fs) //; last exact/lh.
  case=> h' [?][?][?][h3][->]?.
  by exists h'; splits*; exists h1, h3; splits*.
Qed.

Lemma hsub_hstar_id_r (fs : fset D) H Q f :
  (forall x, indom fs x -> f x = x) ->
  (forall d d', d <> d' -> f d = f d' -> ~ indom fs d /\ ~ indom fs d') ->
  hlocal H fs ->
    hsub (Q \* H) f = hsub Q f \* H.
Proof. by move=> *; rewrite hstar_comm (@hsub_hstar_id_l fs) // hstar_comm. Qed.

Fact hsub_hsingle_merge (f : D -> D) (d1 d2 : D) (Hn : d1 <> d2)
  (H1 : f d1 = d1) (H2 : f d2 = d1) 
  (Hdom : forall d, f d = d1 -> d = d1 \/ d = d2)
  (p : loc) (v : val) :
  hsub (p ~(d1)~> v \* p ~(d2)~> v) f = p ~(d1)~> v.
Proof.
  extens. intros h.
  split; intros Hh.
  { unfold hsub in Hh. destruct Hh as (h' & <- & Hvalid & Hh').
    apply hstar_inv in Hh'.
    destruct Hh' as (h1 & h2 & Hh1 & Hh2 & Hdj & ->).
    apply hsingle_inv in Hh1, Hh2. subst h1 h2.
    match goal with |- _ ?hf => enough (hf = (Fmap.single (p, d1) v)) as Htmp end.
    1: rewrite Htmp; apply hsingle_intro.
    apply fmap_extens. intros (pp, dd). simpl. case_if.
    { injection C as <-. subst dd.
      unfold map_fsubst, map_union, map_indom.
      destruct (classicT _) as [ E | E ].
      { destruct (indefinite_description E) as ((ll, d) & EE & E'). 
        simpl in EE. inversion EE. subst ll. rewrite H3.
        case_if; auto. case_if; auto.
      }
      { false E. exists (p, d1). split; auto. case_if. eqsolve. }
    }
    { unfold map_fsubst, map_union, map_indom.
      destruct (classicT _) as [ E | E ]; auto.
      destruct (indefinite_description E) as ((ll, d) & EE & E'). 
      simpl in EE. inversion EE. subst ll.
      case_if; auto. case_if; auto.
    }
  }
  {
    apply hsingle_inv in Hh. subst h.
    unfold hsub. 
    exists (Fmap.single (p, d1) v \u Fmap.single (p, d2) v).
    split.
    1:{
      apply fmap_extens. intros (pp, dd). simpl. case_if.
      { injection C as <-. subst dd.
        unfold map_fsubst, map_union, map_indom.
        destruct (classicT _) as [ E | E ].
        { destruct (indefinite_description E) as ((ll, d) & EE & E'). 
          simpl in EE. inversion EE. subst ll. rewrite H3.
          case_if; auto. case_if; auto.
        }
        { false E. exists (p, d1). split; auto. case_if. eqsolve. }
      }
      { unfold map_fsubst, map_union, map_indom.
        destruct (classicT _) as [ E | E ]; auto.
        destruct (indefinite_description E) as ((ll, d) & EE & E'). 
        simpl in EE. inversion EE. subst ll.
        case_if; auto. case_if; auto.
      }
    }
    split.
    { hnf. intros (pa, da) (pb, db). simpl. intros.
      assert (pa = pb) as -> by eqsolve.
      unfold map_union. 
      repeat case_if; try eqsolve.
      { assert (d1 = da) as <- by eqsolve.
        rewrite H1 in H. 
        assert (f db = d1) as Htmp by eqsolve. apply Hdom in Htmp; eqsolve.
      }
      { assert (d2 = da) as <- by eqsolve.
        rewrite H2 in H. 
        assert (f db = d1) as Htmp by eqsolve. apply Hdom in Htmp; eqsolve.
      }
      { assert (d1 = db) as <- by eqsolve.
        rewrite H1 in H. 
        assert (f da = d1) as Htmp by eqsolve. apply Hdom in Htmp; eqsolve.
      }
      { assert (d2 = db) as <- by eqsolve.
        rewrite H2 in H. 
        assert (f da = d1) as Htmp by eqsolve. apply Hdom in Htmp; eqsolve.
      }
    }
    apply hstar_intro; try apply hsingle_intro.
    apply disjoint_single_single.
    eqsolve.
  }
Qed.

Fact hsub_hpure_comm P H f : hsub (\[P] \* H) f = (\[P] \* hsub H f).
Proof.
  extens. intros h.
  split; intros Hh.
  { unfold hsub in Hh. destruct Hh as (h' & <- & Hvalid & Hh').
    apply hstar_inv in Hh'.
    destruct Hh' as (h1 & h2 & Hh1 & Hh2 & Hdj & ->).
    apply hpure_inv in Hh1. destruct Hh1 as (Hp & ->).
    rewrite union_empty_l in Hvalid |- *.
    rewrite <- union_empty_l.
    apply hstar_intro. 1: by apply hpure_intro.
    2: auto.
    unfold hsub. exists h2. intuition.
  }
  { rewrite <- union_empty_l in Hh.
    apply hstar_inv in Hh.
    destruct Hh as (h1 & h2 & Hh1 & Hh2 & Hdj & E).
    rewrite union_empty_l in E. subst h.
    apply hpure_inv in Hh1. destruct Hh1 as (Hp & ->).
    rewrite union_empty_l.
    unfold hsub in Hh2 |- *. 
    destruct Hh2 as (h' & <- & Hvalid & Hh').
    exists (empty \u h').
    rewrite ! union_empty_l.
    split; auto. split; auto. 
    rewrite <- union_empty_l. apply hstar_intro; auto. by apply hpure_intro.
  }
Qed.

Lemma wp_union Q t fs1 fs2 : 
  disjoint fs1 fs2 ->
  wp fs1 t (fun hr1 => wp fs2 t (fun hr2 => Q (hr1 \u_(fs1) hr2))) = 
  wp (fs1 \u fs2) t Q.
Proof.
  move=> dj.
  apply/himpl_antisym.
  { rewrite {1}/wp. xsimpl=> ? M1.
    rewrite /wp; xsimpl=> ?. apply/hhoare_union=> //= ?.
    by apply wp_equiv. }
  rewrite {1}/wp. xsimpl=> P hh.
  rewrite {1}/wp. xsimpl=> H.
  rewrite /wp.
  move/hhoare_union2: (hh)=> /(_ H dj) ?.
  apply/hhoare_conseq; [eauto|xsimpl|].
  xsimpl*.
Qed.

Lemma wp_single d t Q : 
  wp (single d tt) t Q = 
  wp (single d tt) (fun=> t d) Q.
Proof. by apply/wp_ht_eq=> ? /[! indom_single_eq]->. Qed.

Lemma htriple_union_test1 : forall H Q Q' t fs1 fs2,
  disjoint fs1 fs2 ->
  htriple fs1 t H Q' ->
  Q' ===> (fun hr1 => wp fs2 t (fun hr2 => Q (hr1 \u_(fs1) hr2))) ->
  htriple (fs1 \u fs2) t H Q.
Proof.
  intros.
  apply wp_equiv. rewrite <- wp_union; try assumption.
  apply wp_equiv.
  eapply htriple_conseq. 1: apply H1. all: auto.
Qed.

Lemma htriple_union_test2 : forall H Q Q' t fs1 fs2,
  disjoint fs1 fs2 ->
  htriple fs1 t H Q' ->
  (forall hv, 
    htriple fs2 t (Q' hv) (fun hr2 => Q (hv \u_(fs1) hr2))) ->
  htriple (fs1 \u fs2) t H Q.
Proof.
  intros.
  apply wp_equiv. rewrite <- wp_union; try assumption.
  apply wp_equiv.
  eapply htriple_conseq. 1: apply H1. 1: auto.
  hnf. intros. apply wp_equiv. apply H2. 
Qed.

Lemma htriple_union (fs fs' : fset D) H H' (Q Q' : _ -> hhprop) ht 
  (Hdj : disjoint fs fs')
  (Hcong : forall hv1 hv2, (forall d, indom fs d -> hv1 d = hv2 d) -> 
    Q hv1 ==> Q hv2)
  (Hcong' : forall hv1 hv2, (forall d, indom fs' d -> hv1 d = hv2 d) -> 
    Q' hv1 ==> Q' hv2)
  (Htp : htriple fs ht H Q)
  (Htp' : htriple fs' ht H' Q') :
  htriple (fs \u fs') ht (H \* H') (fun hv => Q hv \* Q' hv).
Proof.
  eapply htriple_conseq. 1: eapply htriple_union_test2. 1: auto.
  1:{ eapply htriple_frame with (H':=H') in Htp. apply Htp. }
  2: auto.
  2: hnf; intros; apply himpl_refl.
  { intros. apply wp_equiv. apply wp_equiv.
    eapply htriple_conseq_frame. 
    2: rewrite -> hstar_comm; apply himpl_refl.
    1: apply Htp'.
    (* simple proof *)
    hnf. intros hv2. 
    rewrite -> hstar_comm. 
    eapply himpl_hstar_trans_l. 2: apply himpl_frame_r.
    { unfold uni. apply Hcong.
      intros. case_if; eqsolve.
    }
    { unfold uni. apply Hcong'.
      intros. case_if; try eqsolve.
      false. eapply disjoint_inv_not_indom_both; eauto.
    }
  }
Qed.

Fact hbig_fset_himpl : forall {A : Type} (fs : fset A) (H H' : A -> hhprop),
  (forall (d : A), indom fs d -> H d ==> H' d) ->
  (\*_(d <- fs) H d) ==> (\*_(d <- fs) H' d).
Proof.
  intros A fs. pattern fs. apply fset_ind; clear fs.
  { introv N. hnf. introv HH. by rewrite -> hbig_fset_empty in *. }
  { introv IH Hni N. hnf. introv HH.
    rewrite -> hbig_fset_update in HH |- *; auto.
    apply hstar_inv in HH.
    destruct HH as (h1 & h2 & Hh1 & HH & Hdj & ->).
    apply hstar_intro; auto.
    { apply N; auto. unfolds indom, map_indom. simpl. unfolds update, map_union. by case_if. }
    { eapply IH. 2: apply HH. intros. apply N. 
      unfolds indom, map_indom. simpl. unfolds update, map_union. by case_if. 
    }
  }
Qed.

Lemma htriple_union_pointwise (fs : fset D) (H : D -> hhprop) (Q : D -> (D -> val) -> hhprop) ht 
  (Hcong : forall d hv1 hv2, hv1 d = hv2 d -> Q d hv1 ==> Q d hv2) :
  forall (Htp : forall d, indom fs d -> htriple (single d tt) ht (H d) (Q d)),
  htriple fs ht (\*_(d <- fs) H d) (fun hv => \*_(d <- fs) (Q d hv)).
Proof.
  pattern fs. apply fset_ind; clear fs; intros.
  { rewrite -> hbig_fset_empty.
    unfold htriple. intros. 
    eapply hhoare_conseq. 1: rewrite -> hhoare0.
    2: xsimpl. 1: xsimpl.
    hnf. intros. xsimpl. by rewrite -> hbig_fset_empty.
  }
  { eapply htriple_conseq.
    1:{ eapply htriple_union.
      1: by apply disjoint_single_of_not_indom.
      3: apply Htp.
      3: apply indom_update.
      3: apply H0.
      3: intros; apply Htp.
      3: rewrite -> indom_update_eq; by right.
      { intros. specialize (H2 _ (indom_single _ _)).
        by apply Hcong.
      }
      { intros. simpl.
        apply hbig_fset_himpl. intros. by apply Hcong, H2.
      }
    }
    { rewrite -> hbig_fset_update; auto. }
    { hnf. intros hv. rewrite -> hbig_fset_update; auto. }
  }
Qed.

Lemma wp_union2 Q t fs1 fs2 : 
  disjoint fs1 fs2 ->
  wp (fs1 \u fs2) t Q ==>
  wp fs1 t (fun=> wp fs2 t Q).
Proof.
  move=> dj.
  rewrite {1}/wp. xsimpl=> P hh.
  rewrite {1}/wp. xsimpl=> H.
  rewrite /wp.
  move/hhoare_union2': (hh)=> /(_ H dj) ?.
  apply/hhoare_conseq; [eauto|xsimpl|].
  xsimpl*.
Qed.

(* Lemma wp_union2 Q t fs1 fs2 : 
  disjoint fs1 fs2 ->
  wp (fs1 \u fs2) t Q ==>
  wp fs1 t (fun hr1 => \exists hv, wp fs2 t (fun hr2 => \[forall d, indom fs1 d -> hr2 d = hv d] \* Q (hr1 \u_(fs1) hr2))).
Proof.
  move=> dj.
  rewrite {1}/wp. xsimpl=> P hh.
  rewrite {1}/wp. xsimpl=> H.
  rewrite /wp.
  move/hhoare_union2: (hh)=> /(_ H dj) ?.
  apply/hhoare_conseq; [eauto|xsimpl|].
  move=> ?. xpull=> ?? HH; xsimpl*.
Qed. *)

Lemma wp0_dep ht Q : wp empty ht Q = \exists hv, Q hv.
Proof.
  rewrite /wp; xpull.
  { move=> ? /(_ \[]) /[! hhoare0_dep]. 
    by rew_heap. }
  move=> ?; xsimpl=> ?. 
  rewrite hhoare0_dep=> ??; eexists; eauto.
Qed.

Lemma wp0 ht Q : wp empty ht (fun=> Q) = Q.
Proof.
  rewrite /wp. xsimpl.
  { move=> ? /(_ \[]) /[! hhoare0]; by rew_heap. }
  move=> ?; by rewrite hhoare0.
Qed.



Notation "'funloc' p '=>' H" :=
  (fun (r:D -> val) => \exists (p : D -> loc), \[r = val_loc \o p] \* H)
  (at level 200, p ident, format "'funloc'  p  '=>'  H") : hprop_scope.

(* ################################################################# *)
(** * WP Generator *)

(** This section defines a "weakest-precondition style characteristic
      formula generator". This technology adapts the technique of
      "characteristic formulae" (originally developed in CFML 1.0)
      to produce weakest preconditions. (The formulae, their manipulation,
      and their correctness proofs are simpler in wp-style.)

    The goal of the section is to define a function [wpgen t], recursively
    over the structure of [t], such that [wpgen t Q] entails [wp t Q].
    Unlike [wp t Q], which is defined semantically, [wpgen t Q] is defined
    following the syntax of [t].

    Technically, we define [wpgen E t], where [E] is a list of bindings,
    to compute a formula that entails [wp (isubst E t)], where [isubst E t]
    denotes the iterated substitution of bindings from [E] inside [t]. *)

(* ================================================================= *)
(** ** Definition of Context as List of Bindings *)

(** In order to define a structurally recursive and relatively
    efficient characteristic formula generator, we need to introduce
    contexts, that essentially serve to apply substitutions lazily. *)

Open Scope liblist_scope.

(* ================================================================= *)
(** ** Definition of [wpgen] *)

(** The definition of [wpgen E t] comes next. It depends on a predicate
    called [mkstruct] for handling structural rules, and on one auxiliary
    definition for each term rule. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [mkstruct] *)

(** Let [formula] denote the type of [wp t] and [wpgen t]. *)

Section WPgen.

Context (fs : fset D).

Definition formula := ((D -> val) -> hhprop) -> hhprop.

Implicit Type F : formula.

(** [mkstruct F] transforms a formula [F] into one that satisfies structural
    rules of Separation Logic. This predicate transformer enables integrating
    support for the frame rule (and other structural rules), in characteristic
    formulae. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q', F Q' \* (Q' \--* Q).

Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. xsimpl. Qed.

Arguments mkstruct_ramified : clear implicits.

Lemma mkstruct_erase : forall Q F,
  F Q ==> mkstruct F Q.
Proof using. unfolds mkstruct. xsimpl. Qed.

Arguments mkstruct_erase : clear implicits.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. unfolds mkstruct. xpull. intros Q. xsimpl Q. xchanges WQ.
Qed.

Lemma mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using.
  intros. unfold mkstruct. xpull. intros Q'. xsimpl Q'.
Qed.

Lemma mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.
Proof using.
  introv WF. unfolds mkstruct. xpull. intros Q'. xchange WF. xsimpl Q'.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Definition of Auxiliary Definition for [wpgen] *)

(** we state auxiliary definitions for [wpgen], one per term construct.
    For simplicity, we here assume the term [t] to be in A-normal form.
    If it is not, the formula generated will be incomplete, that is,
    useless to prove htriples about the term [t]. Note that the actual
    generator in CFML2 does support terms that are not in A-normal form. *)

Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_val (v:D->val) : formula := fun Q =>
  Q v.

Definition wpgen_fun (Fof:(D->val)->formula) : formula := fun Q =>
  \forall (vf : D -> val), \[forall (vx : D -> val) Q', Fof vx Q' ==> wp fs (fun d => trm_app (vf d) (vx d)) Q'] \-* Q vf.

Definition wpgen_fix (Fof:(D->val)->(D->val)->formula) : formula := fun Q =>
  \forall hvf, \[forall hvx Q', Fof hvf hvx Q' ==> wp fs (fun d => trm_app (hvf d) (hvx d)) Q'] \-* Q hvf.

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

Definition wpgen_let (F1:formula) (F2of:(D->val)->formula) : formula := fun Q =>
  F1 (fun hv => F2of hv Q).

Definition wpgen_if (t:D->trm) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[t = fun=> trm_val (val_bool b)] \* (if b then F1 Q else F2 Q).

Definition wpgen_if_trm (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => mkstruct (wpgen_if v F1 F2)).

(* ----------------------------------------------------------------- *)
(** *** Recursive Definition of [wpgen] *)

(** [wpgen E t] is structurally recursive on [t]. Note that this function does
    not recurse through values. Note also that the context [E] gets extended
    when traversing bindings, in the let-binding and the function cases. *)

Definition is_val (t : D -> trm) :=
  exists v, t = fun d => trm_val (v d).

Definition get_val (t : D -> trm) :=
  fun d => match t d with trm_val v => v | _ => arbitrary end.

Lemma is_val_val hv : is_val (fun d => trm_val (hv d)).
Proof. exists __; eauto. Qed.

Definition is_fun (t : D -> trm) :=
  exists x t', t = fun d => trm_fun (x d) (t' d).

Definition is_fix (t : D -> trm) :=
  exists f x t', t = fun d => trm_fix (f d) (x d) (t' d).

Definition is_if (t : D -> trm) :=
  exists t0 t1 t2, t = fun d => trm_if (t0 d) (t1 d) (t2 d).

Definition is_seq (t : D -> trm) :=
  exists t1 t2, t = fun d => trm_seq (t1 d) (t2 d).

Definition is_let (t : D -> trm) :=
  exists x t1 t2, t = fun d => trm_let (x d) (t1 d) (t2 d).

Definition get_var (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_fun x _ | trm_let x _ _ | trm_fix _ x _ => x
    | _ => arbitrary
    end.

Definition get_fun (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_fun _ t | trm_let _ _ t | trm_fix _ _ t => t
    | _ => trm_val 0
    end.

Instance Inhab_trm : Inhab trm.
split.
by exists (trm_val 0).
Qed.

Definition get_f (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_fix f _ _ => f
    | _ => arbitrary
    end.

Definition get_cond (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_if f _ _ => f
    | _ => arbitrary
    end.

Definition get_then (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_if _ f _ => f
    | _ => arbitrary
    end.

Definition get_else (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_if _ _ f => f
    | _ => arbitrary
    end.

Definition get_seq1 (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_seq f _ => f
    | _ => arbitrary
    end.

Definition get_seq2 (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_seq _ f => f
    | _ => arbitrary
    end.

Definition get_letvar (t : D -> trm) :=
  fun d => 
    match t d with 
    | trm_let _ f _ => f 
    | _ => arbitrary
    end.

Definition wpgen (t : D -> trm) : formula :=
  mkstruct (
          If is_val t then wpgen_val (get_val t)
    else If is_fun t then wpgen_fun (fun hv => wp fs (fun d => subst (get_var t d) (hv d) (get_fun t d)))
    else If is_fix t then wpgen_fix (fun hvf hv => wp fs (fun d => subst (get_var t d) (hv d) (subst (get_f t d) (hvf d) (get_fun t d))))
    else If is_if  t then wpgen_if  (get_cond t) (wp fs (fun d => get_then t d)) (wp fs (fun d => get_else t d))
    else If is_seq t then wpgen_seq (wp fs (fun d => get_seq1 t d)) (wp fs (fun d => get_seq2 t d))
    else If is_let t then wpgen_let (wp fs (fun d => get_letvar t d)) (fun hv => wp fs (fun d => subst (get_var t d) (hv d) (get_fun t d)))
    else wp fs t
  ).

Lemma wpgenE `{Inhab D} :
  (forall hv      , wpgen (fun d => trm_val (hv d))        
    = mkstruct (wpgen_val hv))                                                                               *
  (forall x t1    , wpgen (fun d => trm_fun (x d) (t1 d))  
    = mkstruct (wpgen_fun (fun v => wp fs (fun d => subst (x d) (v d) (t1 d)))))                             *
  (forall t1 t2   , wpgen (fun d => trm_seq (t1 d) (t2 d)) 
    = mkstruct (wpgen_seq (wp fs t1) (wp fs t2))) *
  (forall x t1 t2 , wpgen (fun d => trm_let (x d) (t1 d) (t2 d)) 
    = mkstruct (wpgen_let (wp fs t1) (fun v => wp fs (fun d => subst (x d) (v d) (t2 d)))))                  *
  (forall t1 t2   , wpgen (fun d => trm_app (t1 d) (t2 d)) 
    = mkstruct (wp fs (fun d => trm_app (t1 d) (t2 d))))                                                     *
  (forall f x t1  , wpgen (fun d => trm_fix (f d) (x d) (t1 d))
    = mkstruct (wpgen_fix (fun hvf hv => wp fs (fun d => subst (x d) (hv d) (subst (f d) (hvf d) (t1 d)))))) *
  (forall t0 t1 t2, wpgen (fun d => trm_if (t0 d) (t1 d) (t2 d))
    = mkstruct (wpgen_if t0 (wp fs t1) (wp fs t2))).
Proof.
  (do ? split=> * ); rewrite /wpgen.
  { case: classicT=> // -[]; eexists; autos*. }
  { do ? (case: classicT; [(do ? case)=> > /(congr1 (@^~ arbitrary))//|]).
    case: classicT=> // -[]. do ? eexists; autos*. } 
  { do 4? (case: classicT; [(do ? case=> >)=> > /(congr1 (@^~ arbitrary))//|]).
    case: classicT=> // -[]. do ? eexists; autos*. } 
  { do 5? (case: classicT; [(do ? case=> >)=> > /(congr1 (@^~ arbitrary))//|]).
    case: classicT=> // -[]. do ? eexists; autos*. } 
  { do 6? (case: classicT; [(do ? case=> >)=> > /(congr1 (@^~ arbitrary))//|auto]). } 
  { do 2? (case: classicT; [(do ? case=> >)=> > /(congr1 (@^~ arbitrary))//|]).
    case: classicT=> // -[]. do ? eexists; autos*. } 
  do 3? (case: classicT; [(do ? case=> >)=> > /(congr1 (@^~ arbitrary))//|]).
  case: classicT=> // -[]. do ? eexists; autos*. 
Qed.
(* ----------------------------------------------------------------- *)
(** *** Soundness of [wpgen] *)

(** [formula_sound t F] asserts that, for any [Q], the Separation Logic
    judgment [htriple (fun d => F Q) t Q] is valid. In other words, it states that
    [F] is a stronger formula than [wp t].

    The soundness theorem that we are ultimately interested in asserts that
    [formula_sound (isubst E t) (wpgen E t)] holds for any [E] and [t]. *)

Definition formula_sound (t:D -> trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp fs t Q.

Lemma wp_sound : forall t,
  formula_sound t (wp fs t).
Proof using. intros. intros Q. applys @himpl_refl. Qed.

(** One soundness lemma for [mkstruct]. *)

Lemma mkstruct_wp : forall t,
  mkstruct (wp fs t) = (wp fs t).
Proof using.
  intros. applys fun_ext_1. intros Q. applys @himpl_antisym.
  { unfold mkstruct. xpull. intros Q'. applys wp_ramified. }
  { applys mkstruct_erase. }
Qed.

Lemma mkstruct_sound : forall t F,
  formula_sound t F ->
  formula_sound t (mkstruct F).
Proof using.
  introv M. unfolds formula_sound. intros Q'.
  rewrite <- mkstruct_wp. applys* mkstruct_monotone M.
Qed.

(** One soundness lemma for each term construct. *)

Lemma wpgen_fail_sound : forall t,
  formula_sound t wpgen_fail.
Proof using. intros. intros Q. unfold wpgen_fail. xpull. Qed.

Lemma wpgen_val_sound : forall v,
  formula_sound (fun d => trm_val (v d)) (wpgen_val v).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_val. Qed.

Lemma wpgen_fun_sound : forall x t1 Fof,
  (forall hvx, formula_sound (fun d => subst (x d) (hvx d) (t1 d)) (Fof hvx)) ->
  formula_sound (fun d => trm_fun (x d) (t1 d)) (wpgen_fun Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fun. applys @himpl_hforall_l (fun d => val_fun (x d) (t1 d)).
  xchange @hwand_hpure_l.
  { intros. applys @himpl_trans_r. { applys* wp_app_fun. } { applys* M. } }
  { applys wp_fun. }
Qed.

Lemma wpgen_fix_sound : forall f x t1 Fof,
  (forall hvf hvx, formula_sound (fun d => subst (x d) (hvx d) (subst (f d) (hvf d) (t1 d))) (Fof hvf hvx)) ->
  formula_sound (fun d => trm_fix (f d) (x d) (t1 d)) (wpgen_fix Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fix. applys @himpl_hforall_l (fun d => val_fix (f d) (x d) (t1 d)).
  xchange @hwand_hpure_l.
  { intros. applys @himpl_trans_r. { applys* wp_app_fix. } { applys* M. } }
  { applys wp_fix. }
Qed.

Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (fun d => trm_seq (t1 d) (t2 d)) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_seq. applys @himpl_trans wp_seq.
  applys @himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound t1 F1 ->
  (forall hv, formula_sound (fun d => subst (x d) (hv d) (t2 d)) (F2of hv)) ->
  formula_sound (fun d => trm_let (x d) (t1 d) (t2 d)) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_let. applys @himpl_trans wp_let.
  applys @himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_if_sound : forall F1 F2 t0 t1 t2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (fun d => trm_if (t0 d) (t1 d) (t2 d)) (wpgen_if t0 F1 F2).
Proof using.
  introv S1 S2. intros Q. unfold wpgen_if. xpull. intros b ->.
  applys @himpl_trans wp_if. case_if. { applys S1. } { applys S2. }
Qed.

(** The main inductive proof for the soundness theorem. *)

Lemma wpgen_sound : forall t,
  formula_sound t (wpgen t).
Proof using.
  move=> t; rewrite /wpgen.
  case: classicT=> [[?->]|?]; first exact/mkstruct_sound/wpgen_val_sound.
  case: classicT=> [[?][?]->|?]. 
  { rewrite /get_var /get_fun.
    apply/mkstruct_sound/wpgen_fun_sound=> ?.
    exact/wp_sound. }
  case: classicT=> [[?][?][?]->|?]. 
  { rewrite /get_var /get_fun /get_f.
    apply/mkstruct_sound/wpgen_fix_sound=> *; exact/wp_sound. }
  case: classicT=> [[?][?][?]->|?]. 
  { rewrite /get_then /get_else /get_cond.
    apply/mkstruct_sound/wpgen_if_sound=> *; exact/wp_sound. }
  case: classicT=> [[?][?]->|?].
  { rewrite /get_seq1 /get_seq2.
    apply/mkstruct_sound/wpgen_seq_sound=> *; exact/wp_sound. }
  case: classicT=> [[?][?][?]->|?].
  { rewrite /get_letvar /get_var /get_fun.
    apply/mkstruct_sound/wpgen_let_sound=> *; exact/wp_sound. }
  exact/mkstruct_sound/wp_sound.
Qed.

Lemma himpl_wpgen_wp : forall t Q,
  wpgen t Q ==> wp fs t Q.
Proof using.
  introv M. lets N: (@wpgen_sound t). applys* N.
Qed.

(** The final theorem for closed terms. *)

Lemma htriple_of_wpgen : forall t H Q,
  H ==> wpgen t Q ->
  htriple fs t H Q.
Proof using.
  introv M. rewrite <- wp_equiv. xchange M. applys himpl_wpgen_wp.
Qed.

Lemma wp_of_wpgen : forall t H Q,
  H ==> wpgen t Q ->
  H ==> wp fs t Q.
Proof using.
  introv M. rewrite wp_equiv. applys* htriple_of_wpgen.
Qed.


(* ################################################################# *)
(** * Practical Proofs *)

(** This last section shows the techniques involved in setting up the lemmas
    and tactics required to carry out verification in practice, through
    concise proof scripts. *)

(* ================================================================= *)
(** ** Lemmas for Tactics to Manipulate [wpgen] Formulae *)

Lemma xstruct_lemma : forall F H Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_erase. Qed.

Lemma xval_lemma : forall v H Q,
  H ==> Q v ->
  H ==> wpgen_val v Q.
Proof using. introv M. applys M. Qed.

Lemma xlet_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let F1 F2of Q.
Proof using. introv M. xchange M. Qed.

Lemma xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> wpgen_seq F1 F2 Q.
Proof using. introv M. xchange M. Qed.

Lemma xif_lemma : forall b H F1 F2 Q,
  (b = true -> H ==> F1 Q) ->
  (b = false -> H ==> F2 Q) ->
  H ==> (wpgen_if (fun=>b) F1 F2) Q.
Proof using. introv M1 M2. unfold wpgen_if. xsimpl* b. case_if*. Qed.

Lemma xapp_lemma' : forall t t' Q1 H1 H Q,
  (forall d, indom fs d -> t' d = t d) ->
  htriple fs t' H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp fs t Q.
Proof using.
  introv tE M W. rewrite <- wp_equiv in M. xchange W. xchange M.
  rewrite (wp_ht_eq _ t)=> //.
  applys wp_ramified_frame.
Qed.

Lemma xapp_lemma : forall t Q1 H1 H Q,
  htriple fs t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp fs t Q.
Proof using.
  introv M W. rewrite <- wp_equiv in M. xchange W. xchange M.
  applys wp_ramified_frame.
Qed.

Lemma xfun_spec_lemma : forall (S:(D -> val)->Prop) H Q Fof,
  (forall (hvf : D -> val),
    (forall (hvx : D -> val) H' Q', (H' ==> Fof hvx Q') -> 
      htriple fs (fun d => trm_app (hvf d) (hvx d)) H' Q') ->
        S hvf) ->
  (forall hvf, S hvf -> (H ==> Q hvf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M1 M2. unfold wpgen_fun. xsimpl. intros vf N.
  applys M2. applys M1. introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Lemma xfun_nospec_lemma : forall H Q Fof,
  (forall (hvf : D -> val),
      (forall (hvx : D -> val)  H' Q', (H' ==> Fof hvx Q') -> 
        htriple fs (fun d => trm_app (hvf d) (hvx d)) H' Q') ->
      (H ==> Q hvf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M. unfold wpgen_fun. xsimpl. intros vf N. applys M.
  introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Lemma xwp_lemma_fun : forall hv1 (hv2 : D -> val) x t H Q,
  (hv1 = fun d => val_fun (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (t d)) Q ->
  htriple fs (fun d => trm_app (hv1 d) (hv2 d)) H Q.
Proof using.
  introv M1 M2. rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (fun d => subst (x d) (hv2 d) (t d)) Q).
  by applys* wp_app_fun; rewrite M1.
Qed.

Lemma xwp_lemma_wp_fun : forall hv1 (hv2 : D -> val) x t H Q,
  (hv1 = fun d => val_fun (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (t d)) Q ->
  H ==> wp fs (fun d => trm_app (hv1 d) (hv2 d)) Q.
Proof using.
  introv M1 M2. xchange M2.
  xchange (>> wpgen_sound (fun d => subst (x d) (hv2 d) (t d)) Q).
  by applys* wp_app_fun; rewrite M1.
Qed.

Lemma xwp_lemma_fix : forall hv1 (hv2 : D -> val) f x t H Q,
  (hv1 = fun d => val_fix (f d) (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (t d))) Q ->
  htriple fs (fun d => trm_app (hv1 d) (hv2 d)) H Q.
Proof using.
  introv M1 M2. rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (t d))) Q).
  applys* wp_app_fix. by rewrite M1.
Qed.

Lemma xwp_lemma_fix' : forall hv1 (hv2 : D -> val) f x t H Q,
  (hv1 = fun d => trm_fix (f d) (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (subst (f d) (val_fix (f d) (x d) (t d)) (t d))) Q ->
  htriple fs (fun d => trm_app (hv1 d) (hv2 d)) H Q.
Proof using.
  move=> > -> ?.
  rewrite -wp_equiv wp_fix_app2' wp_equiv.
  by apply/xwp_lemma_fix.
Qed.

Lemma xwp_lemma_wp_fix : forall hv1 (hv2 : D -> val) f x t H Q,
  (hv1 = fun d => val_fix (f d) (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (t d))) Q ->
  H ==> wp fs (fun d => trm_app (hv1 d) (hv2 d)) Q.
Proof using.
  introv M1 M2. xchange M2.
  xchange (>> wpgen_sound (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (t d))) Q).
  applys* wp_app_fix. by rewrite M1.
Qed.

Lemma xwp_lemma_wp_fix' : forall hv1 (hv2 : D -> val) f x t H Q,
  (hv1 = fun d => trm_fix (f d) (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (subst (f d) (val_fix (f d) (x d) (t d)) (t d))) Q ->
  H ==> wp fs (fun d => trm_app (hv1 d) (hv2 d)) Q.
Proof using.
  move=> >; rewrite wp_equiv; apply/xwp_lemma_fix'.
Qed.

Lemma xhtriple_lemma : forall t H (Q:(D->val)->hhprop),
  H ==> mkstruct (wp fs t) Q ->
  htriple fs t H Q.
Proof using.
  introv M. rewrite <- wp_equiv. xchange M. unfold mkstruct.
  xpull. intros Q'. applys wp_ramified_frame.
Qed.

End WPgen.

End I_didnt_come_up_with_a_name.

(* ================================================================= *)
(** ** Tactics to Manipulate [wpgen] Formulae *)

(** The tactic are presented in [WPgen]. *)

(** Database of hints for [xapp]. *)

Hint Resolve htriple_get htriple_set htriple_ref htriple_free : htriple.

Hint Resolve htriple_add htriple_div htriple_neg htriple_opp htriple_eq
    htriple_neq htriple_sub htriple_mul htriple_mod htriple_le htriple_lt
    htriple_float_add htriple_float_mkpair htriple_float_fma
    htriple_ge htriple_gt htriple_ptr_add htriple_ptr_add_nat : htriple.

(** [xstruct] removes the leading [mkstruct]. *)

Tactic Notation "xstruct" :=
  applys @xstruct_lemma.

(** [xstruct_if_needed] removes the leading [mkstruct] if there is one. *)

Tactic Notation "xstruct_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Tactic Notation "xval" :=
  xstruct_if_needed; applys @xval_lemma.

Tactic Notation "xlet" :=
  xstruct_if_needed; applys @xlet_lemma.

Tactic Notation "xseq" :=
  xstruct_if_needed; applys @xseq_lemma.

Tactic Notation "xseq_xlet_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q =>
  match F with
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Tactic Notation "xif" :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys @xif_lemma; rew_bool_eq.

(** [xapp_try_clear_unit_result] implements some post-processing for
    cleaning up unused variables. *)

Tactic Notation "xapp_try_clear_unit_result" :=
  try match goal with |- (_ -> val) -> _ => intros _ end.

Tactic Notation "xhtriple" :=
  intros; applys @xhtriple_lemma.

Tactic Notation "xhtriple_if_needed" :=
  try match goal with |- @htriple _ ?t ?H ?Q => applys @xhtriple_lemma end.
    
(** [xapp_simpl] performs the final step of the tactic [xapp]. *)

 Lemma xapp_simpl_lemma {D : Type} : forall (F : formula) (H : hhprop D) Q,
  H ==> F Q ->
  H ==> F Q \* (Q \--* protect Q).
Proof using. introv M. xchange M. unfold protect. xsimpl. Qed.

Tactic Notation "xapp_simpl" :=
  first [ applys @xapp_simpl_lemma; do 2? xsimpl (* handles specification coming from [xfun] *)
        | (do 2? xsimpl); unfold protect; xapp_try_clear_unit_result ].

Tactic Notation "xapp_pre" :=
  xhtriple_if_needed; xseq_xlet_if_needed; xstruct_if_needed.

(** [xapp_nosubst E] implements the heart of [xapp E]. If the argument [E] was
    always a htriple, it would suffice to run [applys @xapp_lemma E; xapp_simpl].
    Yet, [E] might be an specification involving quantifiers. These quantifiers
    need to be first instantiated. This instantiation is achieved by means of
    the tactic [forwards_nounfold_then] offered by the TLC library. *)

Tactic Notation "xapp_nosubst" constr(E) :=
  xapp_pre;
  forwards_nounfold_then E ltac:(fun K => applys @xapp_lemma' K=>//; xapp_simpl).

(** [xapp_apply_spec] implements the heart of [xapp], when called without
    argument. If finds out the specification htriple, either in the hint data
    base named [htriple], or in the context by looking for an induction
    hypothesis. Disclaimer: as explained in [WPgen], the simple
    implementation of [xapp_apply_spec] which we use here does not apply when
    the specification includes premises that cannot be solved by [eauto];
    it such cases, the tactic [xapp E] must be called, providing the
    specification [E] explicitly. This limitation is overcome using more
    involved [Hint Extern] tricks in CFML 2.0. *)

Tactic Notation "xapp_apply_spec" :=
  first [ first [solve [ eauto with lhtriple ]| solve [ eauto with htriple ] ]
        | match goal with H: _ |- _ => eapply H end ].

(** [xapp_nosubst_for_records] is place holder for implementing [xapp] on
    records. It is implemented further on. *)

Ltac xapp_nosubst_for_records tt :=
  fail.

(** [xapp] first calls [xhtriple] if the goal is [htriple t H Q] instead
    of [H ==> wp t Q]. *)

Tactic Notation "xapp_nosubst" :=
  xapp_pre;
  first [ applys @xapp_lemma; [ xapp_apply_spec | xapp_simpl ]
        | xapp_nosubst_for_records tt ].

(** [xapp_try_subst] checks if the goal is of the form:
    - either [forall (r:val), (r = ...) -> ...]
    - or [forall (r:val), forall x, (r = ...) -> ...]

    in which case it substitutes [r] away. *)

Tactic Notation "xapp_try_subst" :=
  try match goal with
  | |- forall (r: _ ->val), (r = _) -> _ => intros ? ->
  | |- forall (r: _ ->val), forall x, (r = _) -> _ =>
      let y := fresh x in intros ? y ->; revert y
  end.

Tactic Notation "xapp" constr(E) :=
  rewrite ?label_single; (* we need to deal with a situations when the
   unary lemma is formulated for fs := single d tt
   but the goal's is ⟨_, single d tt⟩ *)
  xapp_nosubst E; first try typeclasses eauto; xapp_try_subst;
  rewrite -?label_single.

Tactic Notation "xapp" :=
  xapp_nosubst; xapp_try_subst.

Tactic Notation "xapp_big" constr(E) :=
  rewrite -> ! hbig_fset_hstar;
  xapp E=> //; rewrite -?hbig_fset_hstar.

Tactic Notation "xapp_debug" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys @xapp_lemma.

(** [xapp] is essentially equivalent to
    [ xapp_debug; [ xapp_apply_spec | xapp_simpl ] ]. *)

Tactic Notation "xfun" constr(S) :=
  xseq_xlet_if_needed; xstruct_if_needed; applys @xfun_spec_lemma S.

Tactic Notation "xfun" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys @xfun_nospec_lemma.

(** [xvars] may be called for unfolding "program variables as definitions",
    which take the form [Vars.x], and revealing the underlying string. *)

Tactic Notation "xvars" :=
  DefinitionsForVariables.libsepvar_unfold.

(** [xwp_simpl] is a specialized version of [simpl] to be used for
    getting the function [wp] to compute properly. *)

Ltac xwp_simpl :=
  xvars;
  cbn beta delta [
      var_eq subst
      string_dec string_rec string_rect
      sumbool_rec sumbool_rect
      Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
      Bool.bool_dec bool_rec bool_rect ] iota zeta;
  simpl; rewrite ?wpgenE; try (unfold subst; simpl).

Tactic Notation "xwp" :=
  intros;
  first [ applys @xwp_lemma_fun; [ reflexivity | ]
        | applys @xwp_lemma_fix; [ reflexivity | ] 
        | applys @wp_of_wpgen];
  xwp_simpl.

(* ================================================================= *)
(** ** Notations for Triples and [wpgen] *)

Declare Scope wp_scope.

(** Notation for printing proof obligations arising from [wpgen]. *)

Notation "'PRE' H 'CODE' F 'POST' Q" :=
  (H ==> (mkstruct F) Q)
  (at level 8, H at level 0, F, Q at level 0,
    format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

Notation "` F" :=
  (mkstruct F)
  (at level 10,
    format "` F") : wp_scope.

(** Custom grammar for the display of characteristic formulae. *)

Notation "<[ e ]>" :=
  e
  (at level 0, e custom wp at level 99) : wp_scope.

Notation "` F" :=
  (mkstruct F)
  (in custom wp at level 10,
    format "` F") : wp_scope.

Notation "( x )" :=
  x
  (in custom wp,
    x at level 99) : wp_scope.

Notation "{ x }" :=
  x
  (in custom wp at level 0,
    x constr,
    only parsing) : wp_scope.

Notation "x" :=
  x
  (in custom wp at level 0,
    x constr at level 0) : wp_scope.

Notation "'Fail'" :=
  ((wpgen_fail))
  (in custom wp at level 69) : wp_scope.

Notation "'Val' v" :=
  ((wpgen_val v))
  (in custom wp at level 69) : wp_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (in custom wp at level 69,
    x name, (* NOTE: For compilation with Coq 8.12, replace "name" with "ident",
                here and in the next 3 occurrences in the rest of the section. *)
    F1 custom wp at level 99,
    F2 custom wp at level 99,
    right associativity,
  format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'WP' [ d 'in' fs  '=>' t ] '{' v ',' Q '}'" := 
    (wp fs (fun d => t) (fun v => Q)) (at level 30, d name, v name,
  format "'[' 'WP'  [  d '['  'in'  ']' fs   '=>' '/    ' '['  t ']'  ] '/' '['   '{'  v ','  Q  '}' ']' ']' ") : wp_scope.

Notation "'Seq' F1 ; F2" :=
  ((wpgen_seq F1 F2))
  (in custom wp at level 68,
    F1 custom wp at level 99,
    F2 custom wp at level 99,
    right associativity,
    format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.

Notation "'App' '[' d 'in' fs ']' f v1" :=
  ((wp fs (fun d => trm_app (f d) (v1 d))))
  (in custom wp at level 68, d name, f, fs, v1 at level 0) : wp_scope.

Notation "'App' '[' d 'in' fs ']' f v1 v2" :=
  ((wp fs (fun d => trm_app (trm_app (f d) (v1 d)) (v2 d))))
  (in custom wp at level 68, d name, f, fs, v1, v2 at level 0) : wp_scope.

Notation "'If_' v 'Then' F1 'Else' F2" :=
  ((wpgen_if v F1 F2))
  (in custom wp at level 69,
    F1 custom wp at level 99,
    F2 custom wp at level 99,
    left associativity,
    format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Fun' x '=>' F1" :=
  ((wpgen_fun (fun x => F1)))
  (in custom wp at level 69,
    x name,
    F1 custom wp at level 99,
    right associativity,
  format "'[v' '[' 'Fun'  x  '=>'  F1  ']' ']'") : wp_scope.

Notation "'Fix' f x '=>' F1" :=
  ((wpgen_fix (fun f x => F1)))
  (in custom wp at level 69,
    f name, x name,
    F1 custom wp at level 99,
    right associativity,
    format "'[v' '[' 'Fix'  f  x  '=>'  F1  ']' ']'") : wp_scope.

(* ================================================================= *)
(** ** Notation for Concrete Terms *)

(** The custom grammar for [trm] is defined in [LibSepVar]. *)

Declare Scope val_scope.

(** Terms *)

Notation "<{ e }>" :=
  e
  (at level 0, e custom trm at level 99) : trm_scope.

Notation "( x )" :=
  x
  (in custom trm, x at level 99) : trm_scope.

Notation "'begin' e 'end'" :=
  e
  (in custom trm, e custom trm at level 99, only parsing) : trm_scope.

Notation "{ x }" :=
  x
  (in custom trm, x constr) : trm_scope.

Notation "x" := x
  (in custom trm at level 0,
    x constr at level 0) : trm_scope.

Notation "t1 t2" := (trm_app t1 t2)
  (in custom trm at level 30,
    left associativity,
    only parsing) : trm_scope.

Notation "'if' t0 'then' t1 'else' t2" :=
  (trm_if t0 t1 t2)
  (in custom trm at level 69,
    t0 custom trm at level 99,
    t1 custom trm at level 99,
    t2 custom trm at level 99,
    left associativity,
    format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'else' '/' '['   t2 ']' ']'") : trm_scope.

Notation "'if' t0 'then' t1 'end'" :=
  (trm_if t0 t1 (trm_val val_unit))
  (in custom trm at level 69,
    t0 custom trm at level 99, (* at level 0 ? *)
    t1 custom trm at level 99,
    left associativity,
    format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'end' ']'") : trm_scope.

Notation "t1 ';' t2" :=
  (trm_seq t1 t2)
  (in custom trm at level 68,
    t2 custom trm at level 99,
    right associativity,
    format "'[v' '[' t1 ']' ';' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'let' x '=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (in custom trm at level 69,
    x at level 0,
    t1 custom trm at level 99,
    t2 custom trm at level 99,
    right associativity,
    format "'[v' '[' 'let'  x  '='  t1  'in' ']' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'fix' f x1 '=>' t" :=
  (val_fix f x1 t)
  (in custom trm at level 69,
    f, x1 at level 0,
    t custom trm at level 99,
    format "'fix'  f  x1  '=>'  t") : val_scope.

Notation "'fix_' f x1 '=>' t" :=
  (trm_fix f x1 t)
  (in custom trm at level 69,
    f, x1 at level 0,
    t custom trm at level 99,
    format "'fix_'  f  x1  '=>'  t") : trm_scope.

Notation "'fun' x1 '=>' t" :=
  (val_fun x1 t)
  (in custom trm at level 69,
    x1 at level 0,
    t custom trm at level 99,
    format "'fun'  x1  '=>'  t") : val_scope.

Notation "'fun_' x1 '=>' t" :=
  (trm_fun x1 t)
  (in custom trm at level 69,
    x1 at level 0,
    t custom trm at level 99,
    format "'fun_'  x1  '=>'  t") : trm_scope.

Notation "()" :=
  (trm_val val_unit)
  (in custom trm at level 0) : trm_scope.

Notation "()" :=
  (val_unit)
  (at level 0) : val_scope.

(** Notation for Primitive Operations. *)

Notation "'ref'" :=
  (trm_val (val_prim val_ref))
  (in custom trm at level 0) : trm_scope.

Notation "'free'" :=
  (trm_val (val_prim val_free))
  (in custom trm at level 0) : trm_scope.

Notation "'not'" :=
  (trm_val (val_prim val_neg))
  (in custom trm at level 0) : trm_scope.

Notation "! t" :=
  (val_get t)
  (in custom trm at level 67,
    t custom trm at level 99) : trm_scope.

Notation "t1 := t2" :=
  (val_set t1 t2)
  (in custom trm at level 67) : trm_scope.

Notation "t1 + t2" :=
  (val_add t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 .+ t2" :=
  (val_float_add t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "'- t" :=
  (val_opp t)
  (in custom trm at level 57,
    t custom trm at level 99) : trm_scope.

Notation "t1 - t2" :=
  (val_sub t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 * t2" :=
  (val_mul t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 .* t2" :=
  (val_float_mkpair t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "'\fma' t1 t2 t3" :=
  (val_float_fma (val_floatpair t1 t2) t3)
  (in custom trm at level 58) : trm_scope.

Notation "t1 / t2" :=
  (val_div t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 'mod' t2" :=
  (val_mod t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 = t2" :=
  (val_eq t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 <> t2" :=
  (val_neq t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 <= t2" :=
  (val_le t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 < t2" :=
  (val_lt t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 >= t2" :=
  (val_ge t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 > t2" :=
  (val_gt t1 t2)
  (in custom trm at level 60) : trm_scope.

(* ================================================================= *)
(** ** Scopes, Coercions and Notations for Concrete Programs *)

Module ProgramSyntax.

Export NotationForVariables.

Module Vars := DefinitionsForVariables.

Close Scope fmap_scope.
Open Scope string_scope.
Open Scope val_scope.
Open Scope trm_scope.
Open Scope wp_scope.
Coercion string_to_var (x:string) : var := x.

End ProgramSyntax.


(* ================================================================= *)
(** ** Treatment of Functions of 2 and 3 Arguments *)

(** As explained in chapter [Struct], there are different ways to
    support functions of several arguments: curried functions, n-ary
    functions, or functions expecting a tuple as argument.

    For simplicity, we here follow the approach based on curried
    function, specialized for arity 2 and 3. It is possible to state
    arity-generic definitions and lemmas, but the definitions become
    much more technical.

    From an engineering point of view, it is easier and more efficient
    to follow the approach using n-ary functions, as the CFML tool does. *)

(* ----------------------------------------------------------------- *)
(** *** Syntax for Functions of 2 or 3 Arguments. *)

Notation "'fun' x1 x2 '=>' t" :=
  (val_fun x1 (trm_fun x2 t))
  (in custom trm at level 69,
    x1, x2 at level 0,
    format "'fun'  x1  x2  '=>'  t") : val_scope.

Notation "'fix' f x1 x2 '=>' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (in custom trm at level 69,
    f, x1, x2 at level 0,
    format "'fix'  f  x1  x2  '=>'  t") : val_scope.

Notation "'fun_' x1 x2 '=>' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (in custom trm at level 69,
    x1, x2 at level 0,
    format "'fun_'  x1  x2  '=>'  t") : trm_scope.

Notation "'fix_' f x1 x2 '=>' t" :=
  (trm_fix f x1 (trm_fun x2 t))
  (in custom trm at level 69,
    f, x1, x2 at level 0,
    format "'fix_'  f  x1  x2  '=>'  t") : trm_scope.

Notation "'fun' x1 x2 x3 '=>' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
    x1, x2, x3 at level 0,
    format "'fun'  x1  x2  x3  '=>'  t") : val_scope.

Notation "'fun' x1 x2 x3 x4 '=>' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 t))))
  (in custom trm at level 69,
    x1, x2, x3, x4 at level 0,
    format "'fun'  x1  x2  x3  x4  '=>'  t") : val_scope.

Notation "'fun' x1 x2 x3 x4 x5 '=>' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 (trm_fun x5 t)))))
  (in custom trm at level 69,
    x1, x2, x3, x4, x5 at level 0,
    format "'fun'  x1  x2  x3  x4  x5  '=>'  t") : val_scope.

  (* Notation "'fun' x1 x2 x3 x4 x5 x6 '=>' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 (trm_fun x5 (trm_fun x6 t))))))
  (in custom trm at level 69,
    x1, x2, x3, x5, x6 at level 0,
    format "'fun'  x1  x2  x3  x4  x5  x6  '=>'  t") : val_scope. *)

Notation "'fix' f x1 x2 x3 '=>' t" :=
  (val_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
    f, x1, x2, x3 at level 0,
    format "'fix'  f  x1  x2  x3  '=>'  t") : val_scope.

Notation "'fun_' x1 x2 x3 '=>' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
    x1, x2, x3 at level 0, format "'fun_'  x1  x2  x3  '=>'  t") : trm_scope.

Notation "'fun_' x1 x2 x3 x4 '=>' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 t))))
  (in custom trm at level 69,
    x1, x2, x3, x4 at level 0, format "'fun_'  x1  x2  x3  x4  '=>'  t") : trm_scope.

Notation "'fun_' x1 x2 x3 x4 x5 '=>' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 (trm_fun x5 t)))))
  (in custom trm at level 69,
    x1, x2, x3, x4, x5 at level 0,
    format "'fun_'  x1  x2  x3  x4  x5  '=>'  t") : val_scope.

Notation "'fix_' f x1 x2 x3 '=>' t" :=
  (trm_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
    f, x1, x2, x3 at level 0, format "'fix_'  f  x1  x2  x3  '=>'  t") : trm_scope.

(* ----------------------------------------------------------------- *)
(** *** Evaluation Rules for Applications to 2 or 3 Arguments. *)

(** [eval_like] judgment for applications to several arguments. *)

Lemma eval_like_app_fun2 {D:Type} : forall fs (x1 x2 : D -> var) (t1 : D -> trm) (v1 v2 : D -> val),
  (forall d, indom fs d -> x1 d <> x2 d) ->
  eval_like fs 
    (fun d => (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d))))
    (fun d => (val_fun (x1 d) (trm_fun (x2 d) (t1 d))) (v1 d) (v2 d)).
Proof using.
  introv E N. unfolds eval. destruct N as (H1 & H2). split.
  { introv Hin. applys* eval1_app_args.
    { applys eval1_app_fun. 1: reflexivity. applys eval1_fun. }
    { applys* eval1_val. }
    { applys* eval1_app_fun. case_var. 1: specializes E Hin; eqsolve. by apply H1. }
  }
  { auto. }
Qed.

Lemma eval_like_app_fun3 {D:Type} : forall fs (x1 x2 x3 : D -> var) (t1 : D -> trm) (v1 v2 v3 : D -> val),
  (forall d, indom fs d -> x1 d <> x2 d) ->
  (forall d, indom fs d -> x2 d <> x3 d) ->
  (forall d, indom fs d -> x1 d <> x3 d) ->
  eval_like fs 
    (fun d => (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d)))))
    (fun d => (val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t1 d)))) (v1 d) (v2 d) (v3 d)).
Proof using.
  introv N1 N2 N3 H. unfolds eval. destruct H as (H1 & H2). split.
  { introv Hin. applys* eval1_app_args.
    { applys* eval1_app_args.
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. 
        case_var. 1: specializes N1 Hin; eqsolve.
        case_var. 1: specializes N3 Hin; eqsolve. 
        applys eval1_fun.
      }
      { applys* eval1_val. }
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. 
        case_var. 1: specializes N2 Hin; eqsolve. 
        applys eval1_fun.
      }
    }
    { applys* eval1_val. }
    { applys* eval1_app_fun. }
  }
  { auto. }
Qed.

Lemma eval_like_app_fun4 {D:Type} : forall fs (x1 x2 x3 x4 : D -> var) (t1 : D -> trm) (v1 v2 v3 v4 : D -> val),
  (forall d, indom fs d -> 
    ~ eq (x1 d) (x2 d) /\ 
    ~ eq (x1 d) (x3 d) /\ 
    ~ eq (x1 d) (x4 d) /\ 
    ~ eq (x2 d) (x3 d) /\ 
    ~ eq (x2 d) (x4 d) /\ 
    ~ eq (x3 d) (x4 d)) ->
  eval_like fs 
    (fun d => (subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d))))))
    (fun d => (val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (t1 d))))) (v1 d) (v2 d) (v3 d) (v4 d)).
Proof using.
  introv N H. unfolds eval. destruct H as (H1 & H2). split; auto.
  introv Hin. applys* eval1_app_args.
  { applys* eval1_app_args.
    { applys* eval1_app_args.
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. specializes N Hin. repeat (case_var; try eqsolve).
        applys eval1_fun. }
      { applys* eval1_val. }
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. specializes N Hin. repeat (case_var; try eqsolve).
        applys eval1_fun. } }
    { applys* eval1_val. }
    { applys eval1_app_fun. 1: reflexivity. 
      simpl. specializes N Hin. repeat (case_var; try eqsolve).
      applys eval1_fun. } }
  { applys* eval1_val. }
  { applys* eval1_app_fun. }
Qed.

Lemma eval_like_app_fun5 {D:Type} : forall fs (x1 x2 x3 x4 x5 : D -> var) (t1 : D -> trm) (v1 v2 v3 v4 v5 : D -> val),
  (forall d, indom fs d -> 
      ~ eq (x1 d) (x2 d) /\
      ~ eq (x1 d) (x3 d) /\
      ~ eq (x1 d) (x4 d) /\
      ~ eq (x1 d) (x5 d) /\
      ~ eq (x2 d) (x3 d) /\
      ~ eq (x2 d) (x4 d) /\
      ~ eq (x2 d) (x5 d) /\
      ~ eq (x3 d) (x4 d) /\
      ~ eq (x3 d) (x5 d) /\
      ~ eq (x4 d) (x5 d)) ->
  eval_like fs 
    (fun d => (subst (x5 d) (v5 d) (subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d)))))))
    (fun d => (val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (trm_fun (x5 d) (t1 d)))))) (v1 d) (v2 d) (v3 d) (v4 d) (v5 d)).
Proof using.
  introv N H. unfolds eval. destruct H as (H1 & H2). split; auto.
  introv Hin. applys* eval1_app_args.
  { applys* eval1_app_args.
    { applys* eval1_app_args.
      { applys* eval1_app_args.
        { applys eval1_app_fun. 1: reflexivity. 
          simpl. specializes N Hin. repeat (case_var; try eqsolve).
          applys eval1_fun. }
        { applys* eval1_val. }
        { applys eval1_app_fun. 1: reflexivity. 
          simpl. specializes N Hin. repeat (case_var; try eqsolve).
          applys eval1_fun. } }
      { applys* eval1_val. }
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. specializes N Hin. repeat (case_var; try eqsolve).
        applys eval1_fun. } }
    { applys* eval1_val. }
    { applys eval1_app_fun. 1: reflexivity. 
      simpl. specializes N Hin. repeat (case_var; try eqsolve).
      applys eval1_fun. } }
  { applys* eval1_val. }
  { applys* eval1_app_fun. }
Qed.
(* ----------------------------------------------------------------- *)
(** *** Reasoning Rules for Applications to 2 or 3 Arguments *)

(** Weakest preconditions for applications to several arguments. *)

Lemma wp_app_fun2 {D:Type} fs : forall x1 x2 v0 v1 (v2 : D -> val) t1 Q,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (t1 d))) ->
  (forall d, x1 d <> x2 d) ->
  wp fs (fun (d : D) => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d))) Q ==> wp fs (fun d => trm_app (v0 d) (v1 d) (v2 d)) Q.
Proof using. 
  introv EQ1 N. applys @wp_eval_like. 
  rewrite EQ1.
  by apply eval_like_app_fun2. 
Qed.

Lemma wp_app_fun3 {D:Type} fs : forall v0 (v1 : D -> val) v2 v3 x1 x2 x3 t Q,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (x1 d) (x3 d) = false /\ var_eq (x2 d) (x3 d) = false) ->
  wp fs (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q ==>
  wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) Q.
Proof using.
  introv EQ1 N. applys @wp_eval_like. 
  rewrite EQ1.
  apply eval_like_app_fun3.
  all: intros d ?; rewrite -isTrue_eq_false_eq -var_eq_spec; apply N.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Generalization of [xwp] to Handle Functions of Two Arguments *)

(** Generalization of [xwp] to handle functions of arity 2 and 3,
    and to handle weakening of an existing specification. *)

Lemma xwp_lemma_fun2 {D:Type} : forall v0 v1 (v2 : D -> _) x1 x2 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (t d))) ->
  (forall d, var_eq (x1 d) (x2 d) = false) ->
  H ==> wpgen fs (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d)) H Q.
Proof using.
  introv E M1 M2. rewrite <- wp_equiv. xchange M2.
  set (w := @wpgen_sound D).
  xchange (>> w (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))) Q).
  applys* @wp_app_fun2=> d. 
  by move: (M1 d); rewrite var_eq_spec isTrue_eq_false_eq.
Qed.


Lemma xwp_lemma_wp_fun2 {D:Type} : forall v0 v1 (v2 : D -> _) x1 x2 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (t d))) ->
  (forall d, var_eq (x1 d) (x2 d) = false) ->
  H ==> wpgen fs (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d)) Q.
Proof using.
  introv E M1 M2. eapply himpl_trans. 1: apply M2.
  eapply himpl_trans. 2: apply wp_app_fun2; eauto. 2: intros d; rewrite -isTrue_eq_false_eq -var_eq_spec; apply M1.
  by apply wpgen_sound.
Qed.

Lemma xwp_lemma_fun3 {D:Type} : forall v0 (v1 : D -> val) v2 v3 x1 x2 x3 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (x1 d) (x3 d) = false /\ var_eq (x2 d) (x3 d) = false) ->
  H ==> wpgen fs (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) H Q.
Proof using.
  introv E M1 M2. rewrite <- wp_equiv. xchange M2.
  set (w := @wpgen_sound D).
  xchange (>> w (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q).
  applys* @wp_app_fun3.
Qed.

Lemma xwp_lemma_fun4 {D:Type} : forall v0 v1 (v2 : D -> _) v3 v4 x1 x2 x3 x4 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (t d))))) ->
  (forall d, 
    var_eq (x1 d) (x2 d) = false /\ 
    var_eq (x1 d) (x3 d) = false /\ 
    var_eq (x1 d) (x4 d) = false /\ 
    var_eq (x2 d) (x3 d) = false /\ 
    var_eq (x2 d) (x4 d) = false /\ 
    var_eq (x3 d) (x4 d) = false
    ) ->
  H ==> wpgen fs (fun d => subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d) (v4 d)) H Q.
Proof using.
  introv E M1 M2. rewrite <- wp_equiv. xchange M2.
  set (w := @wpgen_sound D).
  xchange (>> w (fun d => subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))))) Q).
  applys @wp_eval_like. 
  rewrite E.
  apply eval_like_app_fun4.
  all: intros d ?; rewrite -?isTrue_eq_false_eq -?var_eq_spec; apply M1.
Qed.

Lemma xwp_lemma_fun5 {D:Type} : forall v0 v1 (v2 : D -> _) v3 v4 v5 x1 x2 x3 x4 x5 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (trm_fun (x5 d) (t d)))))) ->
  (forall d, 
    var_eq (x1 d) (x2 d) = false /\ 
    var_eq (x1 d) (x3 d) = false /\ 
    var_eq (x1 d) (x4 d) = false /\ 
    var_eq (x1 d) (x5 d) = false /\ 
    var_eq (x2 d) (x3 d) = false /\ 
    var_eq (x2 d) (x4 d) = false /\ 
    var_eq (x2 d) (x5 d) = false /\ 
    var_eq (x3 d) (x4 d) = false /\
    var_eq (x3 d) (x5 d) = false /\ 
    var_eq (x4 d) (x5 d) = false
    ) ->
  H ==> wpgen fs (fun d => 
    subst (x5 d) (v5 d) (
      subst (x4 d) (v4 d) (
        subst (x3 d) (v3 d) (
          subst (x2 d) (v2 d) (
            subst (x1 d) (v1 d) 
            (t d)))))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d) (v4 d) (v5 d)) H Q.
Proof using.
  introv E M1 M2. rewrite <- wp_equiv. xchange M2.
  set (w := @wpgen_sound D).
  xchange (>> w (fun d => subst (x5 d) (v5 d) (subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))))) Q).
  applys @wp_eval_like. 
  rewrite E.
  apply eval_like_app_fun5.
  all: intros d ?; rewrite -?isTrue_eq_false_eq -?var_eq_spec; apply M1.
Qed.

Lemma xwp_lemma_wp_fun3{D:Type}  : forall v0 v1 v2 (v3 : D -> _) x1 x2 x3 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (x1 d) (x3 d) = false /\ var_eq (x2 d) (x3 d) = false) ->
  H ==> wpgen fs (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) Q.
Proof using. introv E M1 M2. eapply wp_equiv, xwp_lemma_fun3; eauto. Qed.

Lemma xwp_lemma_wp_fun4 {D:Type} : forall v0 v1 v2 (v3 : D -> _) v4 x1 x2 x3 x4 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (t d))))) ->
  (forall d, 
    var_eq (x1 d) (x2 d) = false /\ 
    var_eq (x1 d) (x3 d) = false /\ 
    var_eq (x1 d) (x4 d) = false /\ 
    var_eq (x2 d) (x3 d) = false /\ 
    var_eq (x2 d) (x4 d) = false /\ 
    var_eq (x3 d) (x4 d) = false
    ) ->
  H ==> wpgen fs (fun d => subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d) (v4 d)) Q.
Proof using. introv E M1 M2. eapply wp_equiv, xwp_lemma_fun4; eauto. Qed.

Lemma xwp_lemma_wp_fun5 {D:Type} : forall (v0 : D -> _) v1 v2 v3 v4 v5 x1 x2 x3 x4 x5 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (trm_fun (x5 d) (t d)))))) ->
  (forall d, 
    var_eq (x1 d) (x2 d) = false /\ 
    var_eq (x1 d) (x3 d) = false /\ 
    var_eq (x1 d) (x4 d) = false /\ 
    var_eq (x1 d) (x5 d) = false /\ 
    var_eq (x2 d) (x3 d) = false /\ 
    var_eq (x2 d) (x4 d) = false /\ 
    var_eq (x2 d) (x5 d) = false /\ 
    var_eq (x3 d) (x4 d) = false /\
    var_eq (x3 d) (x5 d) = false /\ 
    var_eq (x4 d) (x5 d) = false
    ) ->
  H ==> wpgen fs (fun d => 
    subst (x5 d) (v5 d) (
      subst (x4 d) (v4 d) (
        subst (x3 d) (v3 d) (
          subst (x2 d) (v2 d) (
            subst (x1 d) (v1 d) 
            (t d)))))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d) (v4 d) (v5 d)) Q.
Proof using. introv E M1 M2. eapply wp_equiv, xwp_lemma_fun5; eauto. Qed.

Tactic Notation "xwp" :=
  intros;
  first [ applys @xwp_lemma_fun;     [ reflexivity | ]
        | applys @xwp_lemma_wp_fun;  [ reflexivity | ]
        | applys @xwp_lemma_fix;     [ reflexivity | ]
        | applys @xwp_lemma_fix';    [ reflexivity | ]
        | applys @xwp_lemma_wp_fix'; [ reflexivity | ]
        | applys @xwp_lemma_wp_fix;  [ reflexivity | ]
        | applys @xwp_lemma_fun2;    [ reflexivity | reflexivity | ]
        | applys @xwp_lemma_wp_fun2; [ reflexivity | reflexivity | ]
        | applys @xwp_lemma_fun3;    [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_wp_fun3; [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_fun4;    [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_wp_fun4; [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_fun5;    [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_wp_fun5; [ reflexivity | (do ? split); reflexivity | ]
        (* | applys xwp_lemma_wp_fix3; [ reflexivity | (do ? split); reflexivity | ] *)
        | applys @wp_of_wpgen
        | fail 1 "xwp only applies to functions defined using [val_fun] or [val_fix], with at most 3 arguments" ];
  xwp_simpl.

Section For_loop.

Context {Dom : Type}.

Import ProgramSyntax.

Definition For_aux (N : trm) (body : trm) : trm :=
  trm_fix "for" "cnt"
    <{ let "cond" = ("cnt" < N) in 
      if "cond" then 
        let "body" = body in
        "body" "cnt";
        let "cnt" = "cnt" + 1 in 
        "for" "cnt"
      else 0 }>.

Definition While_aux (cond : trm) (body : trm) : trm :=
  trm_fix "while" "tt"
    <{ let "cond" = cond in 
      if "cond" then 
          body;
        "while" "tt"
      else 0 }>.

Definition For_aux' (N : trm) (body : trm) : trm :=
  val_fix "for" "cnt"
    <{ let "cond" = ("cnt" < N) in 
      if "cond" then 
        let "body" = body in
        "body" "cnt";
        let "cnt" = "cnt" + 1 in 
        "for" "cnt"
      else 0 }>.

Definition For (Z : trm) (N : trm) (body : trm) : trm :=
  let f := For_aux N body in <{ f Z }>.

Definition While (cond : trm) (body : trm) : trm :=
  let f := While_aux cond body in <{ f 0 }>.

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Lemma label_union {T : Type} (fs1 fs2 : fset T) l : 
  label (Lab l (fs1 \u fs2)) = label (Lab l fs1) \u label (Lab l fs2).
Proof using.
  elim/fset_ind: fs1=> [|fs x IHfs ?] in fs2 *.
  { by rewrite label_empty ?union_empty_l. }
  by rewrite -update_union_not_r' ?label_update IHfs update_union_not_r'.
Qed.

Lemma Union_label {T D} (fs : fset T) l  (fsi : T -> fset D) :
  label (Lab l (Union fs fsi)) = Union fs (fun t => label (Lab l (fsi t))).
Proof.
  elim/fset_ind: fs.
  { by rewrite ?Union0 label_empty. }
  move=> fs x IHfs ?.
  by rewrite ?Union_upd_fset label_union IHfs.
Qed.

Fact interval_fsubst_offset (L R offset : int) :
  fsubst (interval L R) (fun i => i + offset) = 
  interval (L + offset) (R + offset).
Proof.
  apply fset_extens. intros.
  rewrite indom_fsubst. setoid_rewrite indom_interval.
  split.
  { intros (? & <- & ?). lia. }
  { intros. exists (x-offset). lia. }
Qed.

Hint Resolve eqbxx : lhtriple.

Context `{HD : Inhab Dom}.

Lemma htriple_sequ1 (fs fs' : fset Dom) H H' Q ht ht1 ht2 htsuf ht'
  (Hdj : disjoint fs fs')
  (Htp1 : htriple fs ht1 H (fun=> H'))
  (Hhtsuf : forall d, indom fs d -> htsuf d = ht2 d)
  (Hhtsuf' : forall d, indom fs' d -> htsuf d = ht' d)
  (Htpsuf : htriple (fs \u fs') htsuf H' Q)
  (Hht : forall d, indom fs d -> ht d = trm_seq (ht1 d) (ht2 d))
  (Hht' : forall d, indom fs' d -> ht d = ht' d) :
  htriple (fs \u fs') ht H Q.
Proof.
  apply wp_equiv.
  rewrite <- wp_union; auto.
  rewrite -> wp_ht_eq with (ht1:=ht) (ht2:=fun d => trm_seq (ht1 d) (ht2 d)); auto.
  xwp. xseq.
  apply wp_equiv.
  eapply htriple_conseq.
  1: apply Htp1.
  1: xsimpl.
  1:{ 
    xsimpl. 
    rewrite -> wp_ht_eq with (ht1:=ht2) (ht2:=htsuf).
    2: intros; by rewrite -> Hhtsuf.
    eapply himpl_trans. 
    2: apply wp_conseq with (Q1:=fun v => wp fs' htsuf 
      (fun hr2 : Dom -> val => Q ((v \u_ fs) hr2))).
    2:{ 
      hnf. intros. 
      rewrite -> wp_ht_eq with (ht1:=ht) (ht2:=htsuf); auto.
      intros. rewrite -> Hht'; auto. rewrite -> Hhtsuf'; auto.
    }
    rewrite -> wp_union; auto.
    by apply wp_equiv.
  }
Qed.

Lemma htriple_sequ2 (fs fs' : fset Dom) H Q' Q ht ht1 ht2 htpre ht'
  (Hdj : disjoint fs fs')
  (Hhtpre : forall d, indom fs d -> htpre d = ht1 d)
  (Hhtpre' : forall d, indom fs' d -> htpre d = ht' d)
  (Htppre : htriple (fs \u fs') htpre H Q') (* hv? *)
  (Hht : forall d, indom fs d -> ht d = trm_seq (ht1 d) (ht2 d))
  (Hht' : forall d, indom fs' d -> ht d = ht' d)
  (Htp2 : forall hv, htriple fs ht2 (Q' hv) (fun hr => Q (uni fs' hv hr))) :
  htriple (fs \u fs') ht H Q.
Proof using.
  apply wp_equiv.
  rewrite -> union_comm_of_disjoint. 2: apply Hdj.
  rewrite <- wp_union. 2: rewrite -> disjoint_comm; apply Hdj.
  rewrite -> wp_ht_eq with (ht2:=ht').
  2: apply Hht'.
  rewrite -> wp_ht_eq with (ht2:=htpre).
  2: introv HH; rewrite -> Hhtpre'; try reflexivity; try apply HH.
  apply wp_equiv.

  eapply htriple_conseq.
  3:{ 
    hnf. intros v. 
    eapply himpl_trans.
    1: apply wp_seq.
    rewrite -> wp_ht_eq with (ht1:=ht) (ht2:=fun d => trm_seq (ht1 d) (ht2 d)).
    2: apply Hht.
    apply himpl_refl.
  }
  1:{ 
    apply wp_equiv.
    eapply wp_conseq. hnf. intros.
    match goal with |- himpl _ (wp ?fs _ ?ff) => 
      eapply himpl_trans with (H2:=wp fs htpre ff) end.
    1: apply himpl_refl.
    rewrite -> wp_ht_eq with (ht1:=ht1) (ht2:=htpre).
    2: introv HH; rewrite -> Hhtpre; try reflexivity; try apply HH.
    apply himpl_refl.
  }
  apply wp_equiv in Htppre.
  rewrite -> union_comm_of_disjoint in Htppre. 2: apply Hdj.
  rewrite <- wp_union in Htppre. 2: rewrite -> disjoint_comm; apply Hdj.
  eapply himpl_trans.
  1: apply Htppre.
  apply wp_conseq.
  hnf. intros. apply wp_conseq.
  hnf. intros. 
  xapp=> hv.
  move=> ?; apply:applys_eq_init; f_equal; extens=> ?; rewrite /uni.
  do? case:classicT=> //.
Qed.

Lemma wp_for_aux  i fs fs' ht (H : int -> (Dom -> val) -> hhprop Dom) (Z N : int) C fsi hv0 vr:
  (Z <= i <= N) ->
  (forall j hv1 hv2, i <= j <= N -> (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> H j hv1 = H j hv2) ->
  (forall i j, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi i) (fsi j)) ->
  fs = Union (interval i N) fsi ->
  (forall t, subst "for" t C = C) ->
  (forall t, subst "cnt" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  disjoint fs' fs ->
  (forall x, indom fs' x -> ht x = For i N (trm_fun vr C)) ->
  (forall j hv, Z <= j < N -> H j hv ==> 
    wp
      (fs' \u fsi j) 
      ((fun=> subst vr j C) \u_fs' ht) 
      (fun hr => H (j + 1) (hv \u_(Union (interval Z j) fsi) hr))) ->
  H i hv0 ==> 
    wp
      (fs' \u fs)
      ht 
      (fun hr => H N (hv0 \u_(Union (interval Z i) fsi) hr)).
Proof. 
  move=> + hP Dj -> sfor scnt scond vcnt vfor vcond  + +.
  move: ht hv0 hP.
  induction_wf IH: (upto N) i; rewrite /upto le_zarith lt_zarith in IH.
  move=> ht hv0 hP lN dj htE.
  rewrite -wp_union // (wp_ht_eq _ _ _ htE) /For /For_aux.
  rewrite wp_fix_app2.
  Opaque subst.
  xwp.
  Transparent subst. 
  rewrite vcnt vfor sfor /=.
  xapp; rewrite vcond scnt scond.
  xwp; xif.
  { move=> ?. xwp; xlet.
    apply:himpl_trans; first last.
    { apply: wp_fun. }
    simpl; xwp. xseq.
    Opaque subst.
    apply: himpl_trans; first last.
    { apply wp_app_fun=> ?. reflexivity. }
    simpl; remember (subst vr i C) as sub eqn:subE.
    Transparent subst.
    apply: himpl_trans; first last.
    { apply/wp_conseq=> ?. xwp. xlet. xapp. }
    apply: himpl_trans; first last.
    { apply/wp_conseq=> ?. 
      rewrite hstar_hempty_l. 
      apply himpl_qwand_r=> ?. rewrite /protect. 
      xsimpl=>->.
      rewrite -wp_fix_app2.
      set (ht' := (fun=> For_aux N (trm_fun vr C) (i + 1)) \u_fs' ht).
      rewrite (wp_ht_eq _ ht').
      { apply/wp_conseq=> ?; rewrite (wp_ht_eq _ ht'). xsimpl*.
        by move=> ? IND; rewrite /ht' uni_nin // => /(disjoint_inv_not_indom_both dj). }
        by move=> ??; rewrite /ht' uni_in. }
    rewrite (wp_union (fun hr2 => H N (_ \u_ _ hr2))) //.
    rewrite // intervalU; last lia. 
    rewrite // Union_upd // -?union_assoc; first last.
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; lia. }
      move=> ? [?|?]; subst; apply/Dj; lia. }
    rewrite union_comm_of_disjoint -?union_assoc; first rewrite union_comm_of_disjoint.
    2-3: move: dj; rewrite disjoint_union_eq_l ?disjoint_Union.
    2-3: setoid_rewrite indom_interval=> dj; do ?split.
    2-5: by intros; (apply/dj; lia) + (apply/Dj; lia).
    rewrite -wp_union; first last.
    { move: dj; rewrite disjoint_union_eq_r ?disjoint_Union.
      setoid_rewrite indom_interval=> dj; split=> *; [apply/Dj|apply/dj]; lia. }
    set (ht' := (fun=> subst vr i C) \u_fs' ht).
    rewrite (wp_ht_eq _ ht'); first last.
    { by move=> *; rewrite subE /ht' uni_in. }
    rewrite (wp_ht_eq (_ \u_ _ _) ht'); first last.
    { move=> ??; rewrite /ht' ?uni_nin // => /(@disjoint_inv_not_indom_both _ _ _ _ _); apply; eauto.
      all: rewrite indom_Union; setoid_rewrite indom_interval; do? eexists;eauto; lia. }
    apply: himpl_trans; last apply/wp_union2; first last.
    { move: dj; rewrite disjoint_Union disjoint_comm; apply.
      rewrite indom_interval; lia. }
    have: (Z <= i < N) by lia.
    move: (H0 i hv0)=> /[apply]/wp_equiv S; xapp S.
    move=> hr.
    apply: himpl_trans; first last.
    { apply: wp_conseq=> ?; rewrite uniA=> ?; exact. }
    set (hv0 \u_ _ _); rewrite [_ \u fsi i]union_comm_of_disjoint; first last.
    { rewrite disjoint_Union.
      setoid_rewrite indom_interval=> *; apply/Dj; lia. }
    rewrite -Union_upd // -intervalUr; try lia.
    rewrite union_comm_of_disjoint; first last.
    { move: dj; rewrite ?disjoint_Union; setoid_rewrite indom_interval.
      move=> dj *; apply/dj; lia. }
    apply IH; try lia.
    { move=> *; apply/hP; eauto; lia. }
    { move: dj; rewrite ?disjoint_Union; setoid_rewrite indom_interval.
      move=> dj *; apply/dj; lia. }
    { by move=> *; rewrite uni_in. }
    move=> j ??.
    rewrite (wp_ht_eq _ ((fun=> (subst vr j C)) \u_ fs' ht)); eauto.
    move=> ??; rewrite /uni. case: classicT=> //.
    move=> ???; rewrite ?indom_interval=> ??.
    apply/Dj; lia. }
    move=> ?; have->: i = N by lia.
    xwp; xval.
    rewrite intervalgt ?Union0; last lia.
    rewrite wp0_dep. xsimpl hv0.
    erewrite hP; eauto. lia.
    by move=> ??; rewrite uni_in. 
Qed.

Lemma upd_upd_eq {A B} (f : A -> B) x y y' : 
  upd (upd f x y) x y' = upd f x y'.
Proof. by extens=> ?; rewrite /upd; do ? case: classicT. Qed.

Lemma wp_while_aux i fs fs' ht (H : bool -> int -> (Dom -> val) -> hhprop Dom) (Z N : int) T C fsi s b0 hv0 :
  (forall j b hv1 hv2, (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> H b j hv1 = H b j hv2) ->
  fs = Union (interval i N) fsi ->
  fs' = single s tt ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (forall j, (i <= j < N) -> ~ indom (fsi j) s) ->
  (Z <= i <= N) ->
  (ht s = While C T) ->
  (forall (b : bool) (x : int) hv,
    H b x hv ==>
      wp 
        fs'
        (fun=> C) 
        (fun hc => \[hc s = b] \* H b x hv)) -> 
  (forall x hv, H false x hv ==> \[(x = N)] \* H false x hv) ->
  (forall x hv, H true x hv ==> \[(x < N)] \* H true x hv) ->
  (forall j hv, Z <= j < N ->
    (forall j' b' hv, 
        htriple (fs' \u Union (interval j' N) fsi)
          (upd ht s (While C T)) 
          (H b' j' hv \* \[j < j' <= N])
          (fun hr => H false N (hv \u_(Union (interval Z j') fsi) hr))) ->
    H true j hv ==> 
      wp
        (fs' \u Union (interval j N) fsi) 
        (upd ht s (trm_seq T (While C T))) 
        (fun hr => H false N (hv \u_(Union (interval Z j) fsi) hr))) ->
  H b0 i hv0 ==> 
    wp
      (fs' \u fs)
      ht 
      (fun hr => H false N (hv0 \u_(Union (interval Z i) fsi) hr)).
Proof with autos*.
  move=> HE ->-> swhile scond stt cw cc ct +++ HCi IHf HCi'.
  move: ht hv0 b0. induction_wf IH: (upto N) i; rewrite /upto le_zarith lt_zarith in IH.
  move=> ht hv0 b Dj' ? htsE IHt.
  have htE: forall x, indom (single s tt) x -> ht x = While C T.
  { by move=> ? /[! @indom_single_eq]<-. }
  have?: disjoint (single s tt) (Union (interval i N) fsi).
  { rewrite disjoint_Union=> ?/[! @indom_interval]?.
    rewrite disjoint_comm.
    apply/disjoint_single_of_not_indom/Dj'; lia. }
  rewrite -wp_union // (wp_ht_eq _ _ _ htE) /While /While_aux. 
  rewrite wp_fix_app2.
  Opaque subst.
  xwp.
  Transparent subst.
  rewrite /= cw swhile stt ct.
  xlet.
  move=> ? /HCi; apply/wp_conseq=> hv.
  xpull; case:b => -hvsE.
  { under wp_ht_eq.
    { move=> ? /[! indom_single_eq]<-/[! hvsE] /[! over] //. }
    rewrite -/(himpl _ _).
    Opaque subst.
    xwp.
    Transparent subst.
    xif=> // _.
    rewrite scond. rewrite -/(While_aux _ _).
    rewrite -wp_fix_appapp2 -/(While_aux _ _)-/(While _ _).
    under wp_ht_eq; rewrite -/(himpl _ _).
    { move=> s' /[! indom_single_eq] sE.
      rewrite -(upd_eq _ _ ht s (trm_seq T (While C T))) {2}sE over //. }
    rewrite wp_equiv.
    apply/htriple_conseq; first last; [|clear HCi; eauto|].
    { move=> ?. under wp_ht_eq; rewrite -/(himpl _ _).
      { move=> s'; rewrite indom_Union=> -[?][].
        rewrite indom_interval => /Dj' ??.
        rewrite -(upd_neq _ _ ht s (trm_seq T (While C T))) ?over //.
        move=> ?. by subst. } 
      move=> ?; exact. }
    rewrite -wp_equiv (wp_union (fun hv => H false N (_ \u_ _ hv))) //.
    xpull=> ?.
    apply/IHt; first by lia.
    move=> j' b' ?; apply wp_equiv; xsimpl=> ?.
    apply/IH; try lia.
    { move=> ??; apply/Dj'; lia. }
    { by rewrite upd_eq. }
    move=> > ?.
    rewrite ?upd_upd_eq; exact/IHt. }
  under wp_ht_eq.
  { move=> ? /[! indom_single_eq]<-/[! hvsE] /[! over] //. }
  rewrite -/(himpl _ _).
  xwp; xif=> // _.
  xwp; xval; apply:himpl_trans; [exact/IHf|].
  xsimpl=> ->; rewrite intervalgt ?Union0 ?wp0_dep; last lia.
  by xsimpl hv0; erewrite HE; eauto=> ??; rewrite uni_in.
Qed.

Lemma wp_while_aux_unary i fs' (H : bool -> int -> hhprop Dom) Z N T C s b0 :
  fs' = single s tt ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (Z <= i <= N) ->
  (forall (b : bool) (x : int),
    H b x ==>
      wp 
        fs'
        (fun=> C) 
        (fun hc => \[hc s = b] \* H b x)) -> 
  (forall x, H false x ==> \[(x = N)] \* H false x) ->
  (forall x, H true x ==> \[(x < N)] \* H true x) ->
  (forall j, Z <= j < N ->
    (forall j' b', 
      htriple fs'
        (fun=> While C T)
        (H b' j' \* \[j < j' <= N])
        (fun=> H false N)) ->
    H true j ==> wp fs' (fun=> (trm_seq T (While C T))) (fun=> H false N)) ->
  H b0 i ==> wp fs' (fun=> While C T) (fun=> H false N).
Proof with autos*.
  move=>-> ?????? ? HC Hf HC' IH.
  apply: himpl_trans.
  { apply/(@wp_while_aux i empty (single s tt) (fun=> While C T) (fun b x hv => H b x) _ _ T _ (fun=> empty)); eauto.
    { exact/(fun=> val_unit). }
    { by rewrite UnionN0. }
    move=> ? _ {}/IH IH IH'.
    rewrite UnionN0 union_empty_r.
    rewrite (wp_ht_eq _ (fun=> trm_seq T (While C T))).
    { apply/IH=> j' b.
      move: (IH' j' b (fun=> val_unit)); rewrite -?wp_equiv=> {}IH' ? /IH'.
      rewrite UnionN0 (wp_ht_eq _ (fun=> While C T)) ?union_empty_r //.
      by move=> ?; rewrite indom_single_eq=>->; rewrite upd_eq. }
    by move=> ?; rewrite indom_single_eq=>->; rewrite upd_eq. }
  by rewrite UnionN0 union_empty_r.
Qed.

Lemma wp_for fs fs' ht 
  (H : int -> (Dom -> val) -> hhprop Dom) Z N (C : trm) fsi hv0 (P : hhprop Dom) Q vr :
  (forall j hv, Z <= j < N -> H j hv ==> wp (fs' \u fsi j) ((fun=> subst vr j C) \u_fs' ht) (fun hr => H (j + 1) (hr \u_(fsi j) hv))) ->
  (forall j hv1 hv2, Z <= j <= N -> (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> H j hv1 = H j hv2) ->
  (P ==> H Z hv0) -> 
  (H N ===> Q) ->
  (forall i j, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi i) (fsi j)) ->
  (Z <= N) ->
  fs = Union (interval Z N) fsi ->
  (forall t, subst "for" t C = C) ->
  (forall t, subst "cnt" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  disjoint fs' fs ->
  (forall x, indom fs' x -> ht x = For Z N (trm_fun vr C)) ->
  P ==> wp (fs' \u fs) ht Q.
Proof.
  move=> Hwp Heq HP HQ Dj *.
  apply: himpl_trans; first exact/HP.
  apply: himpl_trans; first last.
  { apply: wp_conseq; exact/HQ. }
  apply: himpl_trans.
  { apply/(@wp_for_aux Z); eauto; first lia.
    clear -Hwp Heq Dj=> i hv lP.
    move=> ? // /Hwp -/(_ lP). apply/wp_conseq=> hr.
    erewrite Heq; try lia; eauto=> ?.
    rewrite intervalUr ?Union_upd // ?indom_union_eq; last lia; first last.
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; lia. }
      move=> ? [?|?]; subst; apply/Dj; lia. }
    have ?: disjoint (Union (interval Z i) fsi) (fsi i).
    { apply/disjoint_of_not_indom_both=> ?; rewrite indom_Union.
      case=> ?; rewrite indom_interval=> -[?].
      apply/disjoint_inv_not_indom_both/Dj; lia. }
    case=> IND. 
    { rewrite uni_in // uni_nin //.
      apply/disjoint_inv_not_indom_both; rewrite 1?disjoint_comm; eauto. }
    rewrite uni_nin ?uni_in //.
    apply/disjoint_inv_not_indom_both; eauto. }
  apply/wp_conseq=> ?; rewrite intervalgt ?Union0 ?uni0 //; by lia.
Qed.

Lemma wp_while fs fs' ht (Inv : bool -> int -> (Dom -> val) -> hhprop Dom) Z N T C fsi s b0 hv0 (P : hhprop Dom) Q :
  (forall (b : bool) (x : int) hv,
    Inv b x hv ==>
      wp 
        fs'
        (fun=> C) 
        (fun hc => \[hc s = b] \* Inv b x hv)) -> 
  (forall x hv, Inv false x hv ==> \[(x = N)] \* Inv false x hv) ->
  (forall x hv, Inv true x hv ==> \[(x < N)] \* Inv true x hv) ->
  (forall j hv, Z <= j < N ->
    (forall j' b' hv, 
      htriple (fs' \u Union (interval j' N) fsi)
        (upd ht s (While C T)) 
        (Inv b' j' hv \* \[j < j' <= N])
        (fun hr => Inv false N (hv \u_(Union (interval Z j') fsi) hr))) ->
      Inv true j hv ==> 
        wp
          (fs' \u Union (interval j N) fsi) 
          (upd ht s (trm_seq T (While C T))) 
          (fun hr => Inv false N (hv \u_(Union (interval Z j) fsi) hr))) ->
  (forall j b hv1 hv2, (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> Inv b j hv1 = Inv b j hv2) ->
  P ==> Inv b0 Z hv0 ->
  Inv false N ===> Q ->
  (Z <= N) ->
  fs = Union (interval Z N) fsi ->
  fs' = single s tt ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (forall j, (Z <= j < N) -> ~ indom (fsi j) s) ->
  (ht s = While C T) ->
  P ==> wp (fs' \u fs) ht Q.
Proof with autos*.
  move=> HwpC HwpF HwpT HwpT' Heq HP HQ *.
  apply: himpl_trans; first exact/HP.
  apply: himpl_trans; first last.
  { apply: wp_conseq; exact/HQ. }
  apply: himpl_trans.
  { apply/(wp_while_aux (i := Z) (ht := ht) _ (T := T)); eauto. lia. }
  apply/wp_conseq=> ?; rewrite intervalgt ?Union0 ?uni0 //; by lia.
Qed.

Hint Resolve hmerge_comm hmerge_assoc : core.

Lemma wp_for_hbig_op fs fs' ht fs''
  Inv
  (R R' : Dom -> hhprop Dom)
  m vd (H : int -> hhprop Dom) (H' : int -> (Dom -> val) -> hhprop Dom) 
  Z N (C : trm) fsi (P : hhprop Dom) Q vr :
  (forall i, hlocal (H i) fs'') ->
  (forall i v, hlocal (H' i v) fs'') ->
  (forall l Q, Z <= l < N -> 
    hlocal Q fs'' ->
    Inv l \* 
    (\*_(d <- fsi l) R d) \* 
    Q \(m, vd) H l ==> 
      wp (fs' \u fsi l) 
          ((fun=> subst vr l C) \u_fs' ht) 
          (fun hr => 
            Inv (l + 1) \* 
            (\*_(d <- fsi l) R' d) \* 
            Q \(m, vd) H' l hr)) ->
  (forall (hv hv' : Dom -> val) m,
    Z <= m < N ->
    (forall i, indom (fsi m) i -> hv(i) = hv'(i)) ->
    H' m hv = H' m hv') ->
  comm m -> assoc m -> (forall x y, (vd x /\ vd y) <-> vd (m x y)) ->
  (P ==>  
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi) R d) \*
    \(m, vd)_(i <- interval Z N) H i) -> 
  (forall hv,
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi) R' d) \* 
    (\(m, vd)_(i <- interval Z N) H' i hv) ==> Q hv) ->
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  (Z <= N) ->
  fs = Union (interval Z N) fsi ->
  (forall t, subst "for" t C = C) ->
  (forall t, subst "cnt" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  disjoint fs' fs ->
  (forall x, indom fs' x -> ht x = For Z N (trm_fun vr C)) ->
  P ==> wp (fs' \u fs) ht Q.
Proof.
  move=> Hl1 Hl2 Hwp Heq CM AS VM HP HQ Dj *.
  apply: himpl_trans; first exact/HP.
  apply: himpl_trans; first last.
  { apply: wp_conseq; exact/HQ. }
  apply/(wp_for
      (fun q hv => 
        Inv q \* 
        (\*_(d <- Union (interval Z q) fsi) R' d) \*
        (\*_(d <- Union (interval q N) fsi) R d) \* 
        (\(m, vd)_(i <- interval Z q) H' i hv) \(m, vd) (\(m, vd)_(i <- interval q N) H i)) _ (fun=> 0)); eauto.
  { clear -Hwp Dj CM AS Heq Hl1 Hl2 VM.
    move=> l hv ?. 
    set (Q := (\(m, vd)_(i <- interval Z l) H' i hv) \(m, vd) (\(m, vd)_(i <- interval (l + 1) N) H i)).
    move: (Hwp l Q)=> IH.
    rewrite {1}intervalUr ?Union_upd //; last lia; autos*.
    have Dj': disjoint (fsi l) (Union (interval Z l) fsi).
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; lia. }
    rewrite hbig_fset_union // (@intervalU l N); last lia.
    rewrite Union_upd //; autos*; rewrite hbig_fset_union //; first last.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; lia. }
    apply/xapp_lemma'; [|rewrite <-wp_equiv; apply/IH; try lia|].
    { reflexivity. }
    { rewrite /Q; apply/hlocal_hmerge; exact/hlocal_hmerge_fset. }
    unfold protect.
    rew_heap.
    xsimpl*.
    suff<-: Q \(m, vd) H l = 
      (\(m, vd)_(i0 <- interval Z l) H' i0 hv) \(m, vd) 
      (\(m, vd)_(i0 <- update (interval (l + 1) N) l tt) H i0).
    { xsimpl=> hr. rewrite /Q.
      rewrite hmerge_assoc // [_ \(m, vd) H' _ _]hmerge_comm //.
      rewrite -hmerge_assoc // => h.
      apply: applys_eq_init; apply/(congr1 (@^~ h)).
      fequal. rewrite intervalUr ?hbig_fset_update //; eauto; last lia.
      { rewrite hmerge_comm; eauto. fequal.
        { apply/hbig_fset_eq=> ? +; rewrite indom_interval=> ?. 
          (apply/Heq; try lia)=> ? ind; rewrite uni_nin //.
          move: ind=> /[swap]; apply/disjoint_inv_not_indom_both/Dj; lia. }
        apply/Heq=> *; try lia; by rewrite uni_in. }
      rewrite indom_interval not_and_eq; right. lia. }
      rewrite /Q hmerge_assoc // [_ \(m, vd) H _]hmerge_comm //.
      rewrite hbig_fset_update ?indom_interval; eauto.
      rewrite not_and_eq; left.
      lia. }
  { move=> q hv hv' ? hvE.
    suff->:
      (\(m, vd)_(i0 <- interval Z q) H' i0 hv') = 
      (\(m, vd)_(i0 <- interval Z q) H' i0 hv) by [].
    apply/hbig_fset_eq=> ?; rewrite indom_interval=> ?. 
    apply/Heq=> *; try lia. apply/eq_sym/hvE.
    rewrite indom_Union; eexists; rewrite indom_interval; autos*. }
  { rewrite [_ Z Z]intervalgt; last lia.
    rewrite Union0 ?hbig_fset_empty hmerge_hempty_l; xsimpl. }
  { move=> ?.
    rewrite [_ N N]intervalgt; last lia.
    rewrite Union0 ?hbig_fset_empty hmerge_hempty_r. xsimpl. }
Qed.

Lemma interval_union y x z : 
  x <= y -> 
  y <= z -> interval x y \u interval y z = interval x z.
Proof.
  move=> +?.
  induction_wf IH: (upto y) x; rewrite /upto le_zarith lt_zarith in IH.
  move=> ?.
  case: (prop_inv (x = y))=> [->|?].
  { rewrite intervalgt; rew_fmap=> //; lia. }
  rewrite intervalU -?update_union_not_r' ?IH -?intervalU //; by lia.
Qed.

Arguments interval_union : clear implicits.

Lemma hbig_fset_Union {A : Type} (fs : fset A) fsi (H : A -> hhprop Dom) : 
  (forall i j, i <> j -> indom fs i -> indom fs j -> disjoint (fsi i) (fsi j)) ->
    \*_(i <- Union fs fsi) H i =
    \*_(i <- fs) \*_(d <- fsi i) H d.
Proof.
  elim/fset_ind: fs. 
  { by rewrite Union0 ?hbig_fset_empty. }
  move=> fs x IHfs Hnotin Hdj.
  have?: disjoint (fsi x) (Union fs fsi).
  { rewrite disjoint_Union=> y ?. apply/Hdj; [ by intros -> | | ]; rewrite indom_update_eq; tauto. }
  rewrite Union_upd // hbig_fset_union // hbig_fset_update // IHfs //.
  intros. apply Hdj=> //; rewrite indom_update_eq; tauto.
Qed.

Lemma valid_subst_not_squash h1 h2 (f : Dom -> Dom) fs1 fs2 : 
  valid_subst (h1 \u h2) (fun x : loc * Dom => (x.1, f x.2)) ->
  (forall x y, x <> y -> indom fs1 x -> indom fs2 y -> f x <> f y) ->
  local fs1 h1 ->
  local fs2 h2 ->
    valid_subst h1 (fun x : loc * Dom => (x.1, f x.2)).
Proof.
  move=> v fP l1 l2.
  case=> ? d1[l d2]/= /[dup]-[->]fE ffE.
  move: (v (l, d1) (l, d2) ffE).
  case: (prop_inv (indom h1 (l, d1))).
  { case: (prop_inv (indom h2 (l, d2))).
    { move=> /l2/fP fN /l1/fN/[! fE].
      by case: (classicT (d1 = d2))=> [->//|/[swap]/[apply] ]. }
    move=> ??. by rewrite fmapU_in1 // fmapU_nin2. }
  case: (prop_inv (indom h1 (l, d2))).
  { move=> /[dup]/l1 fd ??. 
    rewrite fmapU_nin1 // fmapU_in1 // =><-.
    rewrite fmapNone //.
    case: (prop_inv (indom h2 (l, d1))).
    { move/l2/(fP _ _ _ fd); rewrite fE.
      case: (classicT (d2 = d1))=> [?|/[swap]/[apply] ]//.
      by subst. }
    by move/(@fmapNone _ _ _ _)->. }
  by move=> *; rewrite ?fmapNone.
Qed.

Implicit Type (H : hhprop Dom).

Lemma hsub_hstar_squash H1 H2 f fs1 fs2 : 
  hlocal H1 fs1 -> 
  hlocal H2 fs2 -> 
  (forall x y, x <> y -> indom fs1 x -> indom fs2 y -> f x <> f y) ->
    hsub (H1 \* H2) f = hsub H1 f \* hsub H2 f.
Proof.
  move=> l1 l2 fP; extens=> h; split.
  { case=> h'[<-][v][h1][h2][Hh1][Hh2][dj]?; subst.
    have?: valid_subst h1 (fun x : loc * Dom => (x.1, f x.2)).
    { applys* valid_subst_not_squash. }
    have?: valid_subst h2 (fun x : loc * Dom => (x.1, f x.2)).
    { by apply/valid_subst_union_l; eauto. }
    exists 
      (fsubst h1 (fun x => (x.1, f x.2))),
      (fsubst h2 (fun x => (x.1, f x.2))); splits.
    { exists h1; splits*. }
    { exists h2; splits*. }
    { apply/valid_subst_disj; eauto. }
    exact/fsubst_union_valid. }
  case=> ?[?][][h1][<-][v1]?[][h2][<-][v2]?[dj]->.
  have?: valid_subst (h1 \u h2) (fun x : loc * Dom => (x.1, f x.2)).
  { by apply/valid_subst_union; eauto. }
  exists (h1 \u h2); splits=> //.
  { exact/fsubst_union_valid. }
  exists h1 h2; splits=> //.
  apply/disjoint_of_not_indom_both=> -[l d] dm1 dm2.
  case: (disjoint_inv_not_indom_both dj (x := (l, f d))); 
  by rewrite fsubst_valid_indom; exists (l, d).
Qed.

Lemma hsub_hstar_fset_squash {A : Type} (Hi : A -> hhprop Dom) f fsi fs : 
  (forall i, indom fs i -> hlocal (Hi i) (fsi i)) -> 
  (forall x y i j, 
    indom fs i -> 
    indom fs j -> 
    i <> j -> 
    indom (fsi i) x -> 
    indom (fsi j) y -> f x <> f y) ->
    hsub (\*_(i <- fs) Hi i) f = \*_(i <- fs) hsub (Hi i) f.
Proof.
  elim/fset_ind: fs.
  { move=> *; rewrite? hbig_fset_empty (@hsub_idE Dom empty); autos*=> //. }
  move=> fs i IHfs ? hl fP.
  rewrite ?hbig_fset_update // (hsub_hstar_squash f (fs1 := fsi i) (fs2 := Union fs fsi)).
  { rewrite IHfs //.
    { move=> ??; apply/hl; rewrite indom_update_eq; by right. }
    move=> > ???; apply/fP=> //; rewrite indom_update_eq; by right. }
  { apply/hl; rewrite indom_update_eq; by left. }
  { apply/hlocal_hstar_fset=> ??? {}/hl hl ?? /hl ind.
    rewrite indom_Union; eexists; split; eauto. 
    apply/ind; rewrite indom_update_eq; by right. }
  move=> x y ? ind; rewrite indom_Union=> -[j][?]?.
  apply/(fP x y i j)=> //; rewrite ?indom_update_eq; try by (left+right).
  by move=> ?; subst.
Qed.


Lemma hsub_hstar_fset (fs fs' : fset Dom) (f : Dom -> Dom) R R' :
  (fsubst fs' f = fs) ->
  (forall d, indom fs' d -> hlocal (R' d) (single d tt)) ->
  (forall x, indom fs x -> hsub (\*_(d <- filter (fun y _ => f y = x) fs') R' d) f = R x) ->
  hsub (\*_(d <- fs') R' d) f = \*_(d <- fs) R d.
Proof.
  move=>  fsE lR ?.
  have fs'E: fs' = Union fs (fun d => filter (fun y _ => f y = d) fs').
  { apply/fset_extens=> x.
    rewrite indom_Union; split.
    { exists (f x); rewrite -fsE indom_fsubst filter_indom.
      by do ? eexists. }
    by case=> ? [_]; rewrite filter_indom=> -[]. }
  rewrite fs'E hbig_fset_Union; first last.
  { move=> *; apply/disjoint_of_not_indom_both=> ?.
    by rewrite ?filter_indom=> -[?]->[_] ?. }
  rewrite (hsub_hstar_fset_squash _ _ (fun i => filter (fun y : Dom => fun=> f y = i) fs')).
  { exact/hbig_fset_eq. }
  { move=> ??; apply/hlocal_hstar_fset=> ?.
    rewrite filter_indom=> -[]??; subst.
    move=> ? {}/lR lR ?? /lR /[! indom_single_eq]<- //.
    rewrite filter_indom; splits*; by exists. }
  by move=> > ???; rewrite ?filter_indom=> -[_]->[_]->.
Qed.


Lemma fsubst_union_valid' {A B C : Type}  `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) :
  disjoint fm1 fm2 ->
  valid_subst' fm1 f ->
  valid_subst' (fm1 \u fm2) f ->
    fsubst (fm1 \u fm2) f = 
    fsubst fm1 f \u fsubst fm2 f.
Proof.
  move=> dj v1 v2; apply/fmap_extens=> x.
  have v3: valid_subst' fm2 f.
  { move=> ?? ind1 ind2 /v2.
    rewrite ?fmapU_nin1=> [->||] //; rewrite ?indom_union_eq; eauto.
    all: apply/(disjoint_inv_not_indom_both);[|eauto]; autos*. }
  case: (prop_inv (indom (fsubst fm1 f) x))=> [/[dup]?|].
  { rewrite fmapU_in1 // fsubst_valid_indom=> -[]y[]<-?.
    have ind : (indom (fm1 \u fm2) y).
    { rewrite indom_union_eq; by left. }
    rewrite /fsubst {1 3}/fmap_data /map_fsubst.
    case: classicT=> [?|].
    { case: (indefinite_description _)=> ? []/v2/[apply]/(_ ind)->.
      case: classicT=> [?|].
      { case: (indefinite_description _)=> ? []/v1/[apply]-> //.
        by rewrite fmapU_in1. }
      case; by exists y. }
    case; by exists y. }
  move=> /[dup]?; rewrite fsubst_valid_indom.
  move=> ind; rewrite fmapU_nin1 //.
  rewrite /fsubst {1 3}/fmap_data /map_fsubst.
  case: classicT=> [?|].
  { case: (indefinite_description _)=> y [] fE ind1.
    have ind2: ~ indom fm1 y.
    { move=> ind2; apply/ind; by exists y. }
    have ?: indom fm2 y.
    { have: indom (fm1 \u fm2) y by [].
      rewrite indom_union_eq; by case. }
    rewrite fmapU_nin1 //; case: classicT=> [?|]; subst.
    { case: (indefinite_description _)=> ?[]??.
      apply/v3; eauto. }
    case; by exists y. }
    case: classicT=> // ?; case: (indefinite_description _)=> y []<-? [].
    exists y; split=> //.
    suff: indom (fm1 \u fm2) y by [].
    rewrite indom_union_eq; eauto.
Qed.

Lemma valid_subst_union_disjoint' {A B C : Type}  (fm1 fm2 : fmap A B) (f : A -> C) :
  disjoint fm1 fm2 ->
  valid_subst' (fm1 \u fm2) f ->
  valid_subst' fm1 f.
Proof.
  move=> dj v12 ?? ?? /v12.
  rewrite ?fmapU_in1 //; apply; rewrite* indom_union_eq.
Qed. 

Lemma valid_subst_union_disjoint'' {A B C : Type}  (fm1 fm2 : fmap A B) (f : A -> C) :
  disjoint fm1 fm2 ->
  valid_subst' (fm1 \u fm2) f ->
  valid_subst' fm2 f.
Proof.
  move=> dj v12 ?? ?? /v12.
  rewrite ?fmapU_nin1; first (apply; rewrite* indom_union_eq).
  all: apply/disjoint_inv_not_indom_both; [|eauto]; autos*.
Qed. 

Lemma fsubst_union_valid_disj' {A B C : Type}  `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) :
  disjoint fm1 fm2 ->
  valid_subst' (fm1 \u fm2) f ->
    fsubst (fm1 \u fm2) f = 
    fsubst fm1 f \u fsubst fm2 f.
Proof.
  move=> dj v. 
  apply/fsubst_union_valid'=> //.
  exact/(valid_subst_union_disjoint' dj).
Qed.

Lemma fmapN0E A B (fm : fmap A B) : 
  (fm <> empty) = (exists y, indom fm y).
Proof.
  extens; split.
  { move=> neq. apply:not_not_inv; rewrite not_exists_eq=> ind.
    apply/neq/fmap_extens=> /=?.
    apply:not_not_inv; exact/ind. }
  by case=> ? /[swap]->.
Qed.

Lemma fsubst_Union_valid_fset' {A C T : Type} fmj (fmi : T -> fset A)  (f : A -> C) fs :
  valid_subst (Union fs fmi) f ->
  (forall i j : T, i <> j -> disjoint (fmi i) (fmi j)) ->
  (forall i, indom fs i -> fsubst (fmi i) f = fmj i) ->
    fsubst (Union fs fmi) f = Union fs fmj.
Proof.
  move=> v.
  have{v}: valid_subst' (Union fs fmi) f by move=>*; exact/v.
  move=> + dj; elim/fset_ind: fs=> //.
  { by rewrite ?Union0 fsubst_empty. }
  move=> fs x IHfs ? /[! @Union_upd_fset] // fsb fmiE.
  have?: disjoint (fmi x) (Union fs fmi).
  { by rewrite disjoint_Union=> z ?; apply/dj=> ?; subst. }
  rewrite fsubst_union_valid_disj' //.
  rewrite IHfs // ?fmiE // ?indom_update_eq; first by left.
  { by apply/valid_subst_union_disjoint''; [|eauto]. }
  move=> *; apply/fmiE; rewrite* indom_update_eq.
Qed.

Lemma fsubst_Union_valid' {A B C T : Type} fm y `{Inhab B} (fmi : T -> fmap A B)  (f : A -> C) fs :
  valid_subst (Union fs fmi) f ->
  (forall i j : T, i <> j -> disjoint (fmi i) (fmi j)) ->
  (forall i, indom fs i -> fsubst (fmi i) f = fm) ->
  indom fs y ->
    fsubst (Union fs fmi) f = fm.
Proof.
  move=> v.
  have{v}: valid_subst' (Union fs fmi) f by move=>*; exact/v.
  move=> + dj; elim/fset_ind: fs y=> // fs x IHfs ? y /[! @Union_upd] // fsb fmiE; autos*.
  case: (prop_inv (fs = empty))=> [?|/[! fmapN0E]-[y' ?] ]; subst.
  { rewrite Union0 union_empty_r=> /[dup]/fmiE /[swap].
    by rewrite indom_update_eq=> -[->|]. }
  have?: disjoint (fmi x) (Union fs fmi).
  { by rewrite disjoint_Union=> z ?; apply/dj=> ?; subst. }
  rewrite fsubst_union_valid_disj' //.
  rewrite (IHfs y') // ?fmiE ?union_self // ?indom_update_eq; first by left.
  { by apply/valid_subst_union_disjoint''; [|eauto]. }
  move=> *; apply/fmiE; rewrite* indom_update_eq.
Qed.

Arguments fsubst_Union_valid' {_ _ _ _} _ _.

(* map family localization *)
Definition fm_localize {A B C} (fs : fset A) (fmi : A -> fmap C B) := ((fmi \u_ fs) (fun=> empty)).

Lemma Union_localization {A B C} (fs : fset A) (fmi : A -> fmap C B) : 
  (forall i j, indom fs i -> indom fs j -> i <> j -> disjoint (fmi i) (fmi j)) ->
  Union fs fmi = Union fs (fm_localize fs fmi).
Proof.
  intros. unfold Union, fm_localize. apply fold_fset_eq.
  intros. extens. intros. unfold uni. case_if; eqsolve.
Qed.

Fact fm_localization {A B C} (fs : fset A) (fmi : A -> fmap C B) : 
  (forall i j, indom fs i -> indom fs j -> i <> j -> disjoint (fmi i) (fmi j)) ->
  forall i j, i <> j -> disjoint (fm_localize fs fmi i) (fm_localize fs fmi j).
Proof.
  intros. apply disjoint_of_not_indom_both.
  intros. unfold fm_localize, uni in H1, H2. repeat case_if.
  2-4: simpl in H1, H2; unfolds indom, map_indom; eqsolve.
  revert H1 H2. apply disjoint_inv_not_indom_both, H; auto.
Qed.

Lemma Union_eq {A B C} (fs : fset A) (fmi1 fmi2 : A -> fmap C B) : 
  (forall i j, i <> j -> disjoint (fmi1 i) (fmi1 j)) ->
  (forall i j, i <> j -> disjoint (fmi2 i) (fmi2 j)) ->
  (forall x, indom fs x -> fmi1 x = fmi2 x) -> 
  Union fs fmi1 = Union fs fmi2.
Proof.
  move=> ??.
  elim/fset_ind: fs.
  { by rewrite ?Union0. }
  move=> fs x IHfs ? fmiE. rewrite ?Union_upd //; autos*; rewrite IHfs.
  { fequal; apply/fmiE; rewrite* indom_update_eq. }
  move=> *; apply/fmiE; rewrite* indom_update_eq.
Qed.

Lemma Union_eq_fset {A B} (fs : fset A) (fsi1 fsi2 : A -> fset B) : 
  (forall x, indom fs x -> fsi1 x = fsi2 x) -> 
  Union fs fsi1 = Union fs fsi2.
Proof.
  elim/fset_ind: fs.
  { by rewrite ?Union0. }
  move=> fs x IHfs ? fsiE. rewrite ?Union_upd_fset //; autos*; rewrite IHfs.
  { fequal; apply/fsiE; rewrite* indom_update_eq. }
  move=> *; apply/fsiE; rewrite* indom_update_eq.
Qed.

Fact interval_point_segmentation i j :
  Union (interval i j) (fun i => single i tt) = interval i j.
Proof.
  apply fset_extens. intros x. 
  rewrite indom_Union indom_interval.
  setoid_rewrite indom_interval. setoid_rewrite indom_single_eq.
  split. by intros (? & ? & <-). eauto.
Qed.

Lemma hstar_fsetE {A} (fs : fset A) (H : A -> hhprop Dom) h :
  (\*_(d <- fs) H d) h = 
  exists hi, 
    h = Union fs hi /\ 
    (forall i j, i <> j -> disjoint (hi i) (hi j)) /\
    (forall i, indom fs i -> H i (hi i)).
Proof.
  elim/fset_ind: fs=> [|fs x IHfs ?] in h *.
  { extens; rewrite hbig_fset_empty; split.
    { move=> /hempty_inv->; exists (fun _ : A => empty : hheap Dom); splits=> //.
      by rewrite Union0. }
    by case=> ? []/[! @Union0]->. }
  rewrite hbig_fset_update //; extens; split.
  { case=> h1 [h2][?][]/[! IHfs]-[hi][]->[]dj ind[].
    rewrite disjoint_Union=> dj' ->.
    have?: forall j, disjoint h1 ((hi \u_ fs) (fun=> empty) j).
    { move=> ?. rewrite /uni; case: classicT=> // /dj'; autos*. }
    have?: forall i j, i <> j -> disjoint ((hi \u_ fs) (fun=> empty) i) ((hi \u_ fs) (fun=> empty) j).
    { move=> *; rewrite /uni; do ? case: classicT=> //; autos*. }
    exists (upd (hi \u_fs (fun=> empty)) x h1); splits.
    { rewrite Union_upd ?upd_eq; autos*.
      { fequal; apply/Union_eq=> // ??.
        {  move=> *; rewrite /upd; do ? case: classicT=> ?; subst; autos*. } 
        rewrite upd_neq // ?uni_in // => ?; by subst. }
      move=> ? j ?; rewrite /upd; do ? (case: classicT=> ?; subst=> //); autos*. }
    { move=> *; rewrite /upd; do ? case: classicT=> ?; subst; autos*. }
    move=> ?; rewrite indom_update_eq=> -[<-|/[dup]?/ind?].
    { by rewrite upd_eq. }
    rewrite upd_neq ?uni_in // => ?; by subst. }
  case=> hi[->][dj] ind; rewrite Union_upd //; autos*.
  exists (hi x), (Union fs hi); splits=> //.
  { apply/ind; rewrite* indom_update_eq. }
  { rewrite IHfs; exists hi; splits=> // ??.
    apply/ind; rewrite* indom_update_eq. }
  by rewrite disjoint_Union=> *; apply/dj=> ?; subst.
Qed.

Local Notation D := Dom. 
Local Notation hhprop := (hhprop Dom). 

Fact hsinglestar_fset_inv {A : Type} (fs : fset A) : forall (d : D) (p : A -> loc) (v : A -> val) h,
  (\*_(a <- fs) ((p a) ~(d)~> (v a))) h -> 
  h = Union fs (fun a => single ((p a), d) (v a)) /\
  forall a1 a2, indom fs a1 -> indom fs a2 -> a1 <> a2 -> p a1 <> p a2.
Proof.
  intros.
  pose proof H as H'. rewrite hstar_fsetE in H'.
  destruct H' as (hi & Eh & Hdj & HH).
  assert (forall i, indom fs i -> hi i = single (p i, d) (v i)) as HH'.
  { intros. apply HH, hsingle_inv in H0. by rewrite H0. }
  assert (forall a1 a2 : A,
    indom fs a1 -> indom fs a2 -> a1 <> a2 -> p a1 <> p a2) as Hr.
  { intros. apply HH' in H0, H1. pose proof (Hdj _ _ H2) as Htmp.
    rewrite -> H0, H1 in Htmp. intros E'. rewrite E' in Htmp.
    by apply disjoint_single_single_same_inv in Htmp.
  }
  split; try assumption.
  subst h.
  etransitivity. 2: symmetry; apply Union_localization.
  2:{ 
    intros. apply disjoint_single_single. intros ?.
    inversion H3. revert H5. by apply Hr.
  }
  apply Union_eq; try assumption.
  {
    apply fm_localization.
    intros. apply disjoint_single_single. intros ?.
    inversion H3. revert H5. by apply Hr.
  }
  { intros. unfold fm_localize, uni. rewrite HH'; auto. case_if; eqsolve. }
Qed.

Lemma aux {T} fsi i (fmi : T -> hheap D) fs x l :
  (forall z, indom fs z -> local (fsi z) (fmi z)) ->
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  (forall i j, i <> j -> disjoint (fmi i) (fmi j)) ->
  indom fs i -> indom (fsi i) x ->
  fmap_data (Union fs fmi) (l, x) = fmap_data (fmi i) (l, x).
Proof.
  move=> + dj1 dj2.
  elim/fset_ind: fs i=> // fs y IHfs ? t lc.
  have lc': forall z : T, indom fs z -> local (fsi z) (fmi z).
  { move=> *; apply/lc; rewrite* indom_update_eq. }
  rewrite indom_update_eq=> -[<-|].
  { rewrite Union_upd // =>?; autos*; rewrite fmapU_nin2 //.
    rewrite indom_Union=> -[]?[]/[dup]?/lc'/[apply].
    apply/disjoint_inv_not_indom_both; last eauto.
    apply/dj1=> ?; by subst. }
  move=> ind1 ind2.
  have ? : ~ indom (fmi y) (l, x).
  { move/lc=> ind. apply/(disjoint_inv_not_indom_both (dj1 t y _)); eauto.
    { move=> ?; by subst. }
    exact/ind/indom_update. }
  rewrite Union_upd //; autos*; rewrite fmapU_nin1 ?(IHfs t) //.
Qed.

Lemma local_single_fsubst (f : D -> D) h x: 
  local (single x tt) h -> 
  local (single (f x) tt) (fsubst h (fun x => (x.1, f x.2))).
Proof.
  move=> lc >; rewrite fsubst_valid_indom=> -[][??][][->]<-/lc.
  by rewrite ?indom_single_eq=>->.
Qed.

Lemma hlocal_single_hsub (f : D -> D) x H:  
  hlocal H (single x tt) -> 
  hlocal (hsub H f) (single (f x) tt).
Proof. by move=> lc ?[h'][]<-[_]/lc/(local_single_fsubst f). Qed.

Lemma hsub_squash f fs R x y R':
  (f y = x) ->
  indom fs y ->
  (forall x x', x <> x' -> f x = f x' -> indom fs x /\ indom fs x') ->
  (forall d, hlocal (R d) (single d tt)) ->
  (forall d, indom fs d -> f d = x -> hlocal (R' d) (single d tt)) ->
  (forall h d, 
    indom fs d -> 
    f d = x -> 
    local (single d tt) h ->
      R' d h <-> R x (fsubst h (fun z => (z.1, f z.2)))) ->
  hsub (\*_(d <- filter (fun y : D => fun=> f y = x) fs) R' d) f =
  R x.
Proof.
  move=> <- ? fP lR' lR RP.
  extens=> h; split.
  { case=> h' [<-][]/[swap].
    rewrite hstar_fsetE=> -[hi][->][].
    do ? setoid_rewrite filter_indom=> //.
    move=> ? R'h v.
    have R'hiy: R' y (hi y) by apply/R'h.
    have lhiy: local (single y tt) (hi y) by apply/lR.
    rewrite (fsubst_Union_valid' (fsubst (hi y) (fun x0 : loc * D => (x0.1, f x0.2))) y) //;
    try setoid_rewrite filter_indom=> //.
    { apply/RP; eauto. }
    move=> z[]? fE.
    have R'hiz: R' z (hi z) by apply/R'h.
    have lhiz: local (single z tt) (hi z) by apply/lR.
    apply/fmap_extens=> -[l w].
    case: (prop_inv (w = f y))=> [->|].
    { rewrite -{1}fE.
      have hiE: forall l, fmap_data (hi z) (l, z) = fmap_data (hi y) (l, y).
      { move=> {}l. 
        move: (v (l, z) (l, y))=> /= /[! fE]/(_ eq_refl).
        rewrite 
          (@aux _ (fun x => single x tt) z) 
          ?(@aux _ (fun x => single x tt) y) //;
        try setoid_rewrite filter_indom=> //.
        2,4: by move=>*; apply disjoint_single_single.
        all: move=> ?[]??; apply/ lR=> //; exact/R'h. }
      case: (prop_inv (indom (hi z) (l, z)))=> [ind/=|].
      { rewrite /map_fsubst; case: classicT.
        { move=> pf; case: (indefinite_description _)=> -[]/=?? [][]->_/lhiz.
          rewrite indom_single_eq=><-.
          case: classicT=> [?|].
          { case: (indefinite_description _)=> -[]/=?? [][]->_/lhiy.
            by rewrite indom_single_eq=><-. }
          case; exists (l, y); split=> //.
          by rewrite /map_indom -hiE. }
        case; by exists (l, z). }
      move=> ?; rewrite ?fmapNone // fsubst_valid_indom.
      all: move=> -[][??][]/=[]-> _ /[dup].
      { move/lhiy; rewrite indom_single_eq=> <-.
        by rewrite /indom /map_indom -hiE. }
      by move/lhiz; rewrite indom_single_eq=> <-. }
    move=> ?. rewrite ?fmapNone // fsubst_valid_indom=> -[][??][]/=[]_/[swap].
    { by move/lhiy; rewrite indom_single_eq=> <-?; subst. }
    by move/lhiz; rewrite indom_single_eq=> <-?; subst. }
  move=> /[dup] /lR' lh Rh.
  set (h' := 
    Union (filter (fun x _=> f x = f y) fs) (fun d => fsubst h (fun x => (x.1, d)))).
  have ?: forall z,
    indom (filter (fun x0 : D => fun=> f x0 = f y) fs) z ->
    local (single z tt) (fsubst h (fun x0 : loc * D => (x0.1, z))).
  { move=> >; rewrite filter_indom=> _; exact/local_single_fsubst/lh. }
  have?: forall i j : D, i <> j -> disjoint (single i tt) (single j tt).
  { move=> ??; exact/disjoint_single_single. }
  have ?: valid_subst h' (fun x0 => (x0.1, f x0.2)).
  { case=> ? d1[l d2]/=[->]/[dup]fE.
    case: (prop_inv (d1 = d2))=> [->|] // /fP/[apply]-[ind1 ind2].
    case: (prop_inv (f y = f d1))=> [ffE|].
    { have?: forall i j : D,
      i <> j -> disjoint (fsubst h (fun x => (x.1, i))) (fsubst h (fun x => (x.1, j))).
      { move=> *; apply/disjoint_of_not_indom_both=> -[??].
        by rewrite ?fsubst_valid_indom=> /[swap]-[][]/=??[][]_<-_[] ?[][]. }
      rewrite /h' 
      (@aux _ (fun x => single x tt) d1)
      ?(@aux _ (fun x => single x tt) d2)
      ?filter_indom -?fE // -?ffE //=.
      rewrite /map_fsubst. case: classicT=> [pf|].
      { case: (indefinite_description _)=> -[??][]/=[->]/lh.
        rewrite indom_single_eq=><-.
        case: classicT=> [?|].
        { case: (indefinite_description _)=> -[??][]/=[->]/lh.
          by rewrite indom_single_eq=><-. }
        case: pf=> -[]? d'/=[][->]? []; by exists (l, d'). }
      case: classicT=> // /[dup]-[][]? d' /=[][->]??[].
      by exists (l, d'). }
    move=> N; rewrite /h'.
    rewrite ?fmapNone // indom_Union=> -[]?[] /[! @filter_indom]/[! @fsubst_valid_indom].
    all: by case=> ? ffE[][??]/=[][->]?; subst; rewrite -ffE fE in N. }
  have ?: forall i j : D,
    i <> j ->
    disjoint (fsubst h (fun x=> (x.1, i))) (fsubst h (fun x => (x.1, j))).
  { move=> > ?; apply/disjoint_of_not_indom_both=> -[??].
    move/local_single_fsubst=> /(_ _ lh).
    rewrite indom_single_eq=>?; subst.
    move/local_single_fsubst=> /(_ _ lh).
    by rewrite indom_single_eq=>?; subst. }
  have ffE: forall i, f i = f y ->
    fsubst (fsubst h (fun x => (x.1, i))) (fun x => (x.1, f x.2)) = h.
  { move=> ? fE.
    by apply/fsubst_cancel'=> -[??]/= /lh; rewrite indom_single_eq fE=> ->. }
  exists h'; splits=> //.
  { rewrite (fsubst_Union_valid' h y) //; 
    try setoid_rewrite filter_indom=> //.
    by move=> ?[?]?; rewrite ffE. }
  rewrite hstar_fsetE.
  exists (fun d => fsubst h (fun x : loc * D => (x.1, d : D))); splits=> //.
  move=> ?; rewrite filter_indom=> -[]? fE.
  apply/RP=> //; [apply/local_single_fsubst;eauto|].
  by rewrite ffE.
Qed.

Lemma eq_fsubst {A C} (fm : fset A) (f g : A -> C) :
  (forall x, indom fm x -> f x = g x) ->
  fsubst fm f = fsubst fm g.
Proof.
  move=> fE; apply/fmap_extens=> ? /=.
  rewrite /map_fsubst; case: classicT=> [pf|].
  { case: (indefinite_description _)=> ?[]?.
    case: classicT=> [?|].
    { case: (indefinite_description _)=> ?[?].
      by rewrite /map_indom; do ? case: (fmap_data _ _)=> // -[]. }
    case: pf=> y[fE' ?][]; rewrite -fE' fE //; by exists y. }
  case: classicT=> // /[dup]-[y][fE' ?]_[]; rewrite -fE' -fE //; by exists y.
Qed.



Lemma hsub_hstar_can g f H Q : 
  cancel f g ->
  hsub (H \* Q) f = hsub H f \* hsub Q f.
Proof.
  move=> c1; extens.
  have?: forall h : hheap D, valid_subst h (fun x => (x.1, f x.2)).
  { move=> ?; exact/(valid_subst_can c1). }
  split.
  { case=> h'[]<-[]?[h1][h2][?][?][?]->.
    exists 
      (fsubst h1 (fun x : loc * D => (x.1, f x.2))),
      (fsubst h2 (fun x : loc * D => (x.1, f x.2))); splits=> //.
    1-2: exists; splits*.
    { exact/valid_subst_disj. }
    exact/fsubst_union_valid. }
  case=> ?[?][][h1][<-][?]?[][h2][<-][?]?[]?->.
  exists (h1 \u h2); splits.
  { exact/fsubst_union_valid. }
  { exact/valid_subst_union. }
  exists h1, h2; splits=> //; exact/valid_subst_disj_inv.
Qed.

Lemma hsub_hempty f : 
  hsub \[] f = \[] :> hhprop.
Proof.
  extens=> h; split=> [|/hempty_inv->].
  { case=> h'[]<-[]?/hempty_inv->; by rewrite fsubst_empty. }
  by exists (empty : hheap D); rewrite fsubst_empty.
Qed.


Lemma hsub_hstar_fstar_can {A} g f (H : A -> _) (fs : fset A) : 
  cancel f g ->
  hsub (\*_(i <- fs) H i) f = \*_(i <- fs) hsub (H i) f :> hhprop.
Proof.
  move=> c; elim/fset_ind: fs=> [|fs x IHfs ?].
  { by rewrite ?hbig_fset_empty hsub_hempty. }
  by rewrite ?hbig_fset_update // (hsub_hstar_can _ _ c) IHfs.
Qed.

Lemma hstar_fset_eq_restr {A B} (R : B -> hhprop) fs (f : A -> B) : 
  injective_restr fs f ->
  \*_(d <- fs) R (f d) = \*_(d <- fsubst fs f) R d.
Proof.
  elim/fset_ind: fs=> [|fs x IHfs Hnotin] Hinj.
  { by rewrite fsubst_empty ?hbig_fset_empty. }
  replace (fsubst _ _) with (update (fsubst fs f) (f x) tt) 
    by now rewrite fsubst_update_valid_restr.
  pose proof Hinj as Hinj'%inj_restr_update.
  rewrite ?hbig_fset_update // ?IHfs // indom_fsubst=> HH.
  destruct HH as (y & E & Hin). apply Hnotin.
  apply Hinj in E; try (rewrite indom_update_eq; tauto). congruence.
Qed.

Lemma hstar_fset_eq {A B} (R : B -> hhprop) fs (f : A -> B) g : 
  cancel f g ->
  \*_(d <- fs) R (f d) = \*_(d <- fsubst fs f) R d.
Proof.
  move=> c.
  elim/fset_ind: fs=> [|fs x IHfs ?].
  { by rewrite fsubst_empty ?hbig_fset_empty. }
  rewrite (fsubst_update _ _ _ c) ?hbig_fset_update // ?IHfs //.
  by rewrite indom_fsubst=> -[?][]/(can_inj c)->.
Qed.

Lemma hsub_hstar {A} (H : A -> hhprop) (f : D -> D) : 
  hsub (\exists a, H a) f =
  \exists a, hsub (H a) f.
Proof.
  extens=> ?; split.
  { case=> h'[]<- []? []a ?.
    exists a, h'; splits*. }
  case=> a []h'[]<-[]??.
  exists h'; splits*; by exists a.
Qed.



Section WP_for.

Context (fs fs' : fset D).
Context (ht : D -> trm).
Context (Inv : int -> hhprop).
Context (R R' : D -> hhprop).
Context (m : val -> val -> val) (vd : val -> Prop).
Context (H : int -> hhprop).
Context (H' : int -> (D -> val) -> hhprop).
Context (Z N : int).
Context (C : trm).
Context (fsi : int -> fset D).
Context (P : hhprop).
Context (Q : (D -> val) -> hhprop).
Context (vr : var).
Context (fsi' : int -> fset D).
Context (fi  : int -> D -> D).
Context (gi  : int -> D -> D).
Context (f g : D -> D).
Context (ht' : D -> trm).


Hypotheses (CM : comm m) (AS : assoc m) (VM : forall x y, (vd x /\ vd y) <-> vd (m x y)).
Hypotheses Pimpl : 
  (P ==>  
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi) R d) \*
    \(m, vd)_(i <- interval Z N) H i).
Hypothesis ZLN : Z <= N.
Hypotheses fsE : fs = Union (interval Z N) fsi.
Hypotheses fsDfs' : disjoint fs' fs.
Hypotheses htE : forall x, indom fs' x -> ht x = For Z N (trm_fun vr C).

Hypotheses lI  : forall i, hlocal (Inv i) fs'.
Hypotheses lH  : forall i, hlocal (H i) fs'.
Hypotheses lH' : forall i v, hlocal (H' i v) fs'.
Hypotheses lR  : forall i, hlocal (R i) (single i tt).
Hypotheses lR' : forall i, hlocal (R' i) (single i tt).

Definition Fs := Union (interval Z N) fsi'.

Hypotheses C1       : forall i, cancel (fi i) (gi i).
Hypotheses C2       : forall i, cancel (gi i) (fi i).
Hypotheses fiIm     : forall i, fsubst (fsi' i) (fi i) = fsi i.
Hypotheses fRestr   : forall i x, indom (interval Z N) i -> indom (fsi' i) x -> f x = fi i x.
Hypotheses fGlue    : forall x x', x <> x' -> f x = f x' -> indom Fs x /\ indom Fs x'.
Hypotheses fIm      : forall x, indom (fsubst (fs' \u Fs) f) x <-> indom (fs' \u Fs) (g x).
Hypotheses fC       : forall i, indom (fs' \u fs) i -> f (g i) = i.
Hypotheses fid      : forall i, indom fs' i -> f i = i.
Hypotheses giid      : forall i j, indom fs' i -> gi j i = i.
Hypotheses ht'E     : ht' \o f = ht.
Hypotheses fs'Dfsi' : forall i, indom (interval Z N) i -> disjoint (fsi' i) fs'.
Hypotheses fsDfsi' : forall i, indom (interval Z N) i -> disjoint (fsi i) fs'.
Hypotheses fsi'D : forall i j, i <> j -> disjoint (fsi' i) (fsi' j).

Hypotheses Qimpl : 
  forall hv,
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi) R' d) \* 
    (\(m, vd)_(i <- interval Z N) H' i (hv \o f)) ==> Q hv.

Hypotheses HE :   
  forall (hv hv' : D -> val) m, 
    Z <= m < N ->
    (forall i, indom (fsi' m) i -> hv(i) = hv'(i)) ->
      H' m hv = H' m hv'.
Hypothesis IH : (forall l Q, Z <= l < N -> 
    Inv l \* 
    (\*_(d <- fsi l) R d) \* 
    Q \(m, vd) H l ==> 
      wp (fs' \u fsi l) 
        ((fun=> subst vr l C) \u_fs' ht) 
        (fun hr => 
            Inv (l + 1) \* 
            (\*_(d <- fsi l) R' d) \* 
            Q \(m, vd) H' l (hr \o f))).


Definition Gi (x : D) :=
  match classicT (exists i, indom (interval Z N) i /\ indom (fsi' i) x) with 
  | left P => 
    let '(@exist _ _ a _) := indefinite_description P in gi a
  | _ => id
  end.

Lemma Gi_in i x : 
  indom (interval Z N) i ->
  indom (fsi' i) x ->
    Gi x = gi i.
Proof.
  move=> ??; rewrite /Gi; case: classicT=> [?|[] ].
  { case: (indefinite_description _)=> j [] ? /=.
    case: (prop_inv (i = j))=> [->|]// /fsi'D.
    move/(@disjoint_inv_not_indom_both _ _ _ _ _)/[apply].
    by case. }
  by exists i.
Qed.

Arguments Gi_in : clear implicits.
  

Lemma hsub_P :
  hsub (
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi') hsub (R (f d)) (Gi d)) \*
    \(m, vd)_(i <- interval Z N) H i) f = 
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi) R d) \*
    \(m, vd)_(i <- interval Z N) H i.
Proof.
  rewrite (@hsub_hstar_id_l _ fs') //; first last.
  { move=> > /fGlue/[apply]-[??]. 
    split; apply/disjoint_inv_not_indom_both; [|eauto| |eauto];
    by rewrite /= /Fs disjoint_Union. }
  rewrite (@hsub_hstar_id_r _ fs') //; first last.
  { exact/hlocal_hmerge_fset. }
  { move=> > /fGlue/[apply]-[??]. 
    split; apply/disjoint_inv_not_indom_both; [|eauto| |eauto];
    by rewrite /= /Fs disjoint_Union. }
  do ? fequals. 
  erewrite hsub_hstar_fset; first reflexivity.
  { rewrite (fsubst_Union_valid_fset' fsi) //.
    { move=> x1 x2; case:(prop_inv (x1 = x2))=>[->|]//.
      move/fGlue/[apply]=>-[]; rewrite /Fs/ indom/map_indom.
      by do ? case: (fmap_data _ _)=> // -[]. }
      move=> ??; rewrite -fiIm; apply/eq_fsubst=> ? /fRestr.
      exact. }
  { move=> d; rewrite indom_Union=> -[i][??]?.
    case=> ?[<-][?]/lR /(local_single_fsubst (Gi d)).
    rewrite (Gi_in i) // (@fRestr i) // ?C1 //. }
  move=> x ind.
  set (B := hbig_fset _ _ _).
  have->: B = 
    \*_(d <- filter (fun y _ => f y = x) 
      (Union (interval Z N) fsi')) hsub (R x) (Gi d).
  { by apply/hbig_fset_eq=> ?; rewrite filter_indom=> -[_]->. }
  have[y]: exists y, indom Fs y /\ f y = x.
  { move: ind; rewrite indom_Union=> -[i][?].
    rewrite -fiIm indom_fsubst=>-[z][<-]?; exists z; split.
    { rewrite /Fs indom_Union; by exists i. }
    exact/fRestr. }
  case=> ? <-.
  apply/hsub_squash=> //.
  { move=> d; rewrite indom_Union=> -[i][]??<-.
    rewrite (Gi_in i) // -{2}[d](C1 i) (@fRestr i) //.
    exact/hlocal_single_hsub. }
  move=> h d; rewrite indom_Union=> -[i][]??<- lh.
  rewrite (Gi_in i) //; split.
  { case=> h' []<-[?] Rh.
    rewrite fsubst_cancel' // => -[]??/= /(lR Rh).
    rewrite indom_single_eq=> <-.
    by rewrite {1}[f d](@fRestr i) // C1. }
  move=> Rh; eexists; splits*.
  { rewrite fsubst_cancel' // => -[]??/= /lh.
    rewrite indom_single_eq=> <-.
    by rewrite {1}[f d](@fRestr i) // C1. }
  by case=> ??[??] /=[->]/(congr1 (fi i))/[! C2]->.
Qed.

Lemma fsubst_fs :  fsubst Fs f = fs.
Proof.
  rewrite /Fs fsE (fsubst_Union_valid_fset' fsi) //.
  { move=> x1 x2; case:(prop_inv (x1 = x2))=>[->|]//.
    move/fGlue/[apply]=>-[]; rewrite /Fs/ indom/map_indom.
    by do ? case: (fmap_data _ _)=> // -[]. }
  move=> ??; rewrite -fiIm; apply/eq_fsubst=> ? /fRestr.
  exact.
Qed.

Lemma fsubst_fsi i :  fsubst (fsi i) (gi i) = fsi' i.
Proof. by rewrite -fiIm fsubst_cancel' // => ?? /[! C1]. Qed.


Lemma fsubst_fs' : fsubst fs' f = fs'.
Proof.
  rewrite (eq_fsubst _ id) //; apply/fmap_extens=> x.
  by rewrite fsubst_valid_eq // => ??->.
Qed.

Lemma fsubst_fs'_gi l : fsubst fs' (gi l) = fs'.
Proof.
  rewrite (eq_fsubst _ id)=> [|?/giid] //; apply/fmap_extens=> x.
  by rewrite fsubst_valid_eq // => ??->.
Qed.

Lemma fsubst_fs'_fi l : fsubst fs' (fi l) = fs'.
Proof.
  rewrite (eq_fsubst _ id)=> [|?/(giid l) {1}<- /[! C2] ] //; apply/fmap_extens=> x.
  by rewrite fsubst_valid_eq // => ??->.
Qed.

Lemma fsubst_fs'Ufs : fsubst (fs' \u Fs) f = fs' \u fs.
Proof.
  rewrite fsubst_union_valid_disj' ?fsubst_fs' ?fsubst_fs // /Fs ?disjoint_Union //.
  move=> >; rewrite /indom /map_indom.
  by do 2? case: (fmap_data _ _)=> // -[].
Qed.

Lemma fsubst_fs'Ufsi i : indom (interval Z N) i -> fsubst (fs' \u fsi i) (gi i) = fs' \u fsi' i.
Proof.
  move=> ?.
  rewrite fsubst_union_valid_disj' ?fsubst_fs'_gi ?fsubst_fsi // 1?disjoint_comm.
  { exact/fsDfsi'. }
  by move=> > ?? /(can_inj (C2 _))->.
Qed.


Lemma hsub_Q :
  (fun v => hsub (
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi') hsub (R' (f d)) (Gi d)) \*
    \(m, vd)_(i <- interval Z N) H' i (v \o f)) f) = fun v =>
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi) R' d) \*
    \(m, vd)_(i <- interval Z N) H' i (v \o f).
Proof.
  apply/fun_ext_1=> ?.
  rewrite (@hsub_hstar_id_l _ fs') //; first last.
  { move=> > /fGlue/[apply]-[??]. 
    split; apply/disjoint_inv_not_indom_both; [|eauto| |eauto];
    by rewrite /= /Fs disjoint_Union. }
  rewrite (@hsub_hstar_id_r _ fs') //; first last.
  { exact/hlocal_hmerge_fset. }
  { move=> > /fGlue/[apply]-[??]. 
    split; apply/disjoint_inv_not_indom_both; [|eauto| |eauto];
    by rewrite /= /Fs disjoint_Union. }
  do ? fequals.
  erewrite hsub_hstar_fset; first reflexivity.
  { by rewrite -fsE -fsubst_fs. }
  { move=> d; rewrite indom_Union=> -[i][??]?.
    case=> ?[<-][?]/lR' /(local_single_fsubst (Gi d)).
    by rewrite (Gi_in i) // (@fRestr i) // C1. }
  move=> x ind.
  set (B := hbig_fset _ _ _).
  have->: B = 
    \*_(d <- filter (fun y _ => f y = x) 
      (Union (interval Z N) fsi')) hsub (R' x) (Gi d).
  { by apply/hbig_fset_eq=> ?; rewrite filter_indom=> -[_]->. }
  have[y]: exists y, indom Fs y /\ f y = x.
  { move: ind; rewrite indom_Union=> -[i][?].
    rewrite -fiIm indom_fsubst=>-[z][<-]?; exists z; split.
    { rewrite /Fs indom_Union; by exists i. }
    exact/fRestr. }
  case=> ? <-.
  apply/hsub_squash=> //.
  { move=> d; rewrite indom_Union=> -[i][]??<-.
    rewrite (Gi_in i) // -{2}[d](C1 i) (@fRestr i) //.
    exact/hlocal_single_hsub. }
  move=> h d; rewrite indom_Union=> -[i][]??<- lh.
  rewrite (Gi_in i) //; split.
  { case=> h' []<-[?] Rh.
    rewrite fsubst_cancel' // => -[]??/= /(lR' Rh).
    rewrite indom_single_eq=> <-.
    by rewrite {1}[f d](@fRestr i) // C1. }
  move=> Rh; eexists; splits*.
  { rewrite fsubst_cancel' // => -[]??/= /lh.
    rewrite indom_single_eq=> <-.
    by rewrite {1}[f d](@fRestr i) // C1. }
  by case=> ??[??] /=[->]/(congr1 (fi i))/[! C2]->.
Qed.

Lemma hsub_Pi l Q' : 
  hlocal Q' fs' ->
  Z <= l < N ->
  hsub (
    Inv l \* 
    (\*_(d <- fsi' l) R (f d)) \* 
    Q' \(m, vd) H l) (gi l) = 
  Inv l \* 
  (\*_(d <- fsi' l) hsub (R (f d)) (gi l)) \* 
  Q' \(m, vd) H l.
Proof.
  move=> ??.
  rewrite (@hsub_hstar_id_l _ fs') //; first last.
  { by move=> > /[swap] /(can_inj (C2 l))->. }
  { by move=> ? /giid. }
  rewrite (@hsub_hstar_id_r _ fs') //; first last.
  { exact/hlocal_hmerge. }
  { by move=> > /[swap] /(can_inj (C2 l))->. }
  { by move=> ? /giid. }
  by rewrite (hsub_hstar_fstar_can _ _ (C2 _)).
Qed.

Lemma hsub_Qi l Q' : 
  hlocal Q' fs' ->
  Z <= l < N ->
  (fun v => hsub (
    Inv (l + 1) \* 
    (\*_(d <- fsi' l) R' (f d)) \* 
    Q' \(m, vd) H' l v) (gi l)) = 
  fun v => Inv (l + 1) \* 
  (\*_(d <- fsi' l) hsub (R' (f d)) (gi l)) \* 
  Q' \(m, vd) H' l v.
Proof.
  move=> ??; apply/fun_ext_1=> ?.
  rewrite (@hsub_hstar_id_l _ fs') //; first last.
  { by move=> > /[swap] /(can_inj (C2 l))->. }
  { by move=> ? /giid. }
  rewrite (@hsub_hstar_id_r _ fs') //; first last.
  { exact/hlocal_hmerge. }
  { by move=> > /[swap] /(can_inj (C2 l))->. }
  { by move=> ? /giid. }
  by rewrite (hsub_hstar_fstar_can _ _ (C2 _)).
Qed.

Lemma wp_for_hbig_op_na_bis :
  (forall t, subst "for" t C = C) ->
  (forall t, subst "cnt" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
    P ==> wp (fs' \u fs) ht Q.
Proof.
  move=> *.
  apply: himpl_trans; first exact/Pimpl.
  apply: himpl_trans; first last.
  { apply: wp_conseq=> hv; exact/Qimpl. }
  rewrite -hsub_P -hsub_Q -fsubst_fs'Ufs.
  rewrite wp_equiv. apply (htriple_hsub g (Q:= fun v => _ \* _ \* \(m, vd)_(i <- _) _ _ v))=> //.
  { move=> ?; rewrite fsubst_fs'Ufs; exact/fC. }
  { move=> hv hv' hvE. do 2? fequal. apply/hbig_fset_eq=> i /[dup]?.
    rewrite indom_interval=> ?.
    apply/HE=> // ??; apply/hvE; rewrite indom_union_eq /Fs indom_Union.
    right; by exists i. }
  { move=> > /fGlue/[apply]-[]; rewrite ?indom_union_eq.
    split; by right. }
  rewrite -wp_equiv.
  apply/wp_for_hbig_op; first last.
  all: try eassumption.
  { by move=> ? /= /[dup]/htE<-/fid->. }
  { by rewrite /Fs disjoint_Union. }
  { reflexivity. }
  { move=> ??; exact. }
  { move=> ?; exact. }
  move=> l Q' ??.
  have/[dup]->: forall R, 
    \*_(d <- fsi' l) (fun x => hsub (R (f x)) (Gi x)) d = 
    \*_(d <- fsi' l) (fun x => hsub (R (f x)) (gi l)) d.
  { move=> ?.
    apply/hbig_fset_eq=> ??; fequals.
    rewrite (Gi_in l) // indom_interval; lia. }
  move->. rewrite -hsub_Pi // -hsub_Qi // -fsubst_fs'Ufsi ?indom_interval; last lia.
  rewrite wp_equiv.
  have vE: forall v: D-> val, v = (v \o gi l) \o fi l.
  { by move=> ?; extens=> ?; rewrite /= C1. }
  apply/htriple_conseq; [|eauto|move=> v ?; rewrite {2}(vE v); exact].
  apply (htriple_hsub (fi l) (Q := fun v => _ \* _ \* _ \(m, vd) _ (v \o _))).
  { by move=> *; rewrite C1. }
  { move=> > hvE; do 3? fequal; apply/HE=> // i ind.
    apply/hvE; rewrite indom_union_eq -fiIm indom_fsubst; right.
    by exists i. }
  { by move=> ?? /[swap]/(can_inj (C2 _)). }
  { move=> x. rewrite fsubst_fs'Ufsi ?indom_interval; last lia.
    rewrite ?indom_union_eq -fiIm indom_fsubst. 
    split=> -[].
    { move=> /[dup]/(giid l){2}<- /[! C2]; by left. }
    { move=> ?; right; by exists x. }
    { move=> /[dup]/(giid l){1}<- /[! C1]; by left. }
    case=> ? []/(can_inj (C1 _))->; by right. }
  have: forall R : _ -> hhprop,
    \*_(d <- fsi' l) R (f d) =
    \*_(d <- fsi l) R d.
  { move=> ?. rewrite -fiIm -(hstar_fset_eq _ _ (C1 _)).
    apply/hbig_fset_eq=> ? /fRestr-> //.
    rewrite indom_interval; lia. }
  move=> /[dup]->->; rewrite -wp_equiv.
  have ->:
    (fun v => Inv (l + 1) \* (\*_(d <- fsi l) R' d) \* Q' \(m, vd) H' l (v \o fi l)) = 
    fun v => Inv (l + 1) \* (\*_(d <- fsi l) R' d) \* Q' \(m, vd) H' l (v \o f).
  { apply/fun_ext_1=> ?; do 3? fequal.
    apply/HE=> // ? /= /fRestr-> //; rewrite indom_interval.
    lia. }
  erewrite wp_ht_eq; eauto=> d /=.
  rewrite indom_union_eq=> -[].
  { by move/[dup]=> /giid-> ?; rewrite ?uni_in. }
  move=> ind; rewrite ?uni_nin /=.
  { rewrite (@fRestr l) ?C2 //; first (rewrite indom_interval; lia). 
    move: ind.
    by rewrite -fiIm -{1}[d](C2 l) (fsubst_indom _ _ (C1 _) (C2 _)). }
  { move: ind; apply/disjoint_inv_not_indom_both/fsDfsi'.
    by rewrite indom_interval; lia. }
  rewrite -(fsubst_indom _ _ (C1 l) (C2 l)) C2 fsubst_fs'_fi.
  move: ind; apply/disjoint_inv_not_indom_both/fsDfsi'.
  by rewrite indom_interval; lia.
Qed. 

End WP_for.

End For_loop.

Notation "'while' C '{' T '}'"  :=
  (While C T)
  (in custom trm at level 69,
    C, T at level 0,
    format "'[' while  C ']'  '{' '/   ' '[' T  '}' ']'") : trm_scope.

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N (trm_fun i t))
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Section I_didnt_come_up_with_a_name.


Context {D : Type}.

Record fset_htrm := FH {
  fs_of : fset D;
  ht_of : D -> trm;
}.

From mathcomp Require Import seq.

Local Notation HD := (labeled D).

Fixpoint fset_of (fs_hts : labSeq fset_htrm) : fset (HD) :=
  if fs_hts is (Lab i fs_ht) :: fs_hts then 
    label (Lab i (fs_of fs_ht)) \u fset_of fs_hts
  else empty.

Fixpoint fset_of' (fs_hts : seq fset_htrm) : fset D :=
  if fs_hts is fs_ht :: fs_hts then 
    fs_of fs_ht \u fset_of' fs_hts
  else empty.

Fixpoint fset_of'' (fs_hts : seq fset_htrm) : fset D :=
  match fs_hts with
  | fs_ht :: nil => fs_of fs_ht 
  | fs_ht :: fs_hts =>  fs_of fs_ht \u fset_of'' fs_hts
  | _ => empty
  end.

Lemma fset_of''E : fset_of'' = fset_of'.
Proof. by extens; elim=> // ? [/=|?? /=-> //] /[! union_empty_r]. Qed.


Fixpoint htrm_of (fs_hts : labSeq fset_htrm) (ld : HD) : trm :=
  if fs_hts is (Lab i fs_ht) :: fs_hts then 
    If i = lab ld /\ indom (fs_of fs_ht) (el ld) then
      ht_of fs_ht (el ld)
    else htrm_of fs_hts ld
  else 0.

Fixpoint htrm_of' (fs_hts : seq fset_htrm) (d : D) : trm :=
  if fs_hts is fs_ht :: fs_hts then 
    If indom (fs_of fs_ht) d then
      ht_of fs_ht d
    else htrm_of' fs_hts d
  else 0.

Fixpoint htrm_of'' (fs_hts : seq fset_htrm) : D -> trm :=
  match fs_hts with 
  | fs_hts :: nil => [eta ht_of fs_hts]
  | fs_ht :: fs_hts => fun d => 
    If indom (fs_of fs_ht) d then
        ht_of fs_ht d
      else htrm_of'' fs_hts d
  | nil => fun=> 0
  end.

Arguments htrm_of'': simpl nomatch.
Arguments htrm_of'': simpl nomatch.

Lemma htrm_of''E : forall h d, indom (fset_of' h) d -> htrm_of'' h d = htrm_of' h d.
Proof.
  elim=> //? [/= _ ?|?? + ].
  { rewrite indom_union_eq=> -[] //; by case: classicT. }
  move=> IH d /=; rewrite indom_union_eq.
  case: classicT=> [|?[]//].
  { by rewrite /htrm_of''; case: classicT. }
  move=> IN; move: (IH d); rewrite /htrm_of'' /= => -> //.
  case: classicT=> //.
Qed.

Lemma fset_of_cons fs_ht fs_hts l : 
    fset_of ((Lab l fs_ht) :: fs_hts) = 
    label (Lab l (fs_of fs_ht)) \u fset_of fs_hts.
Proof. by []. Qed.

Lemma fset_of_nil : 
    fset_of nil = empty.
Proof. by []. Qed.

Definition nwp (fs_hts : labSeq fset_htrm) Q := wp (fset_of fs_hts) (htrm_of fs_hts) Q.

Definition eld : HD -> D := @el _.
Definition eld' : labeled D -> D := @el _.

Coercion eld : HD >-> D.
Coercion eld' : labeled >-> D.

Lemma eqbxx l : lab_eqb l l = true.
Proof. by case: l=> ??; rewrite /lab_eqb Z.eqb_refl Z.eqb_refl. Qed.

Lemma lab_neqd l l' : is_true (negb (lab_eqb l' l)) -> l <> l'.
Proof. by move=> /[swap]->; rewrite eqbxx. Qed.

Lemma lab_eqbP l l' : lab_eqb l l' -> l = l'.
Proof. 
  rewrite /lab_eqb istrue_and_eq -?bool_eq_true_eq ?Z.eqb_eq=> -[].
  by case: l  l'=> ?? []??/=->->. 
Qed.

Lemma lab_eqb_sym l l' :  lab_eqb l l' = lab_eqb l' l.
Proof. by rewrite /lab_eqb Z.eqb_sym [l.2 =? _]Z.eqb_sym. Qed.

Lemma fset_htrm_label_remove_disj l fs_hts fs : 
    disjoint
      (label (Lab l fs))
      (fset_of (LibLabType.remove fs_hts l)).
Proof.
  elim: fs_hts=> //= -[]l' fs_ht fs_hts IHfs_hts.
  case: ssrbool.ifP=> /= // /lab_neqd.
  rewrite disjoint_union_eq_r; split=> //.
  apply/disjoint_of_not_indom_both=> -[]??.
  by rewrite ?indom_label_eq=> /[swap]-[]<- ? [].
Qed.

Definition lookup (s : labSeq fset_htrm) (l : labType) : labeled fset_htrm := 
  let fshts := [seq lt <- s | lab_eqb (lab lt) l] in  
  let fshts := map (fun '(Lab _ x)=> x) fshts in 
  Lab l (FH (fset_of'' fshts) (htrm_of' fshts)).

Definition lookup' (s : labSeq fset_htrm) (l : labType) : labeled fset_htrm := 
  let fshts := [seq lt <- s | lab_eqb (lab lt) l] in  
  let fshts := map (fun '(Lab _ x)=> x) fshts in 
  Lab l (FH (fset_of'' fshts) (htrm_of'' fshts)).

Lemma lookup_cons_ht x xs l d :
  indom (fs_of x) d -> 
  ht_of (el (lookup (Lab l x :: LibLabType.remove xs l) l)) d = ht_of (el (Lab l x)) d.
Proof.
  case: x=> ??/= ?.
  elim: xs=> /= [|[]??/=]; rewrite eqbxx /=.
  { rewrite /lookup /=; by case: classicT. }
  by case: classicT.
Qed.

Lemma lookup_cons_fs x xs l :
  fs_of (el (lookup (Lab l x :: LibLabType.remove xs l) l)) = fs_of x.
Proof.
  case: x=> ??/=.
  elim: xs=> /= [|[]???/=]; rewrite eqbxx /=.
  { by rew_fmap. }
  case: ssrbool.ifP=> //=.
  case: ssrbool.ifP=> //=.
Qed.
  

Lemma fset_htrm_lookup_remove l fs_hts : 
  let fs_ht := lookup fs_hts l in
  let fs    := fs_of (el fs_ht) in 
    fset_of fs_hts = 
    label (Lab l fs) \u 
    fset_of (LibLabType.remove fs_hts l).
Proof.
  move=> /=. rewrite fset_of''E.
  elim: fs_hts=> /= [|[]?? fs_hts IHfs_hts]/=.
  { rewrite label_empty. by rew_fmap. }
  rewrite lab_eqb_sym.
  case: ssrbool.ifP=> /= [/lab_eqbP<-|/ssrbool.negbT/lab_neqd ?].
  { by rewrite label_union union_assoc -IHfs_hts. }
  rewrite IHfs_hts -?union_assoc [label _ \u label _]union_comm_of_disjoint //.
  apply/disjoint_of_not_indom_both=> -[??]/[swap]. 
  by rewrite ?indom_label_eq=> -[<-]_[].
Qed.

Lemma lookup_eq l fs_hts (d : HD) : 
  let fs_ht := lookup fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    indom (label (Lab l fs)) d ->
      htrm_of fs_hts d = ht d.
Proof.
  case: d=> ld d /=; rewrite indom_label_eq fset_of''E=> -[]<-. 
  elim: fs_hts=> // -[]/=?? fs_hts IHfs_hts.
  case: ssrbool.ifP=> /= [/lab_eqbP->|/ssrbool.negbT/lab_neqd ?].
  { rewrite indom_union_eq; case: classicT=> [[]_+_|/[swap]-[?[]|]//].
    { by case:classicT. }
    by case: classicT=> [??[]//|] ? /IHfs_hts. }
  case: classicT=> // -[]?; by subst.
Qed.

Lemma remove_eq l fs_hts (d : HD) : 
  let fs_ht := lookup fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    indom (fset_of (LibLabType.remove fs_hts l)) d ->
      htrm_of fs_hts d = htrm_of (LibLabType.remove fs_hts l) d.
Proof.
  move=> fs_ht fs ht.
  move/(@disjoint_inv_not_indom_both _ _ _ _ _): (fset_htrm_label_remove_disj l fs_hts fs).
  move/[apply]; rewrite {}/fs {}/ht {}/fs_ht /= -/(not _).
  case: d=> ld d /=; rewrite indom_label_eq not_and_eq fset_of''E.
  elim: fs_hts=> // -[]/=?? fs_hts IHfs_hts.
  case: ssrbool.ifP=> /= [/lab_eqbP->|/ssrbool.negbT/lab_neqd ?].
  { rewrite indom_union_eq not_or_eq.
    have->: forall A B C, A \/ B /\ C <-> (A \/ B) /\ (A \/ C) by autos*.
    case=> /[swap]/IHfs_hts; case: classicT; autos*. }
  case: classicT; autos*.
Qed.

Lemma indom_label l (fs : fset D) l' x :
  indom (label (Lab l fs)) (Lab l' x) -> l' = l.
Proof. rewrite* @indom_label_eq. Qed.

Lemma indom_remove l fs_hts l' x :
  indom (fset_of (LibLabType.remove fs_hts l)) (Lab l' x) -> l' <> l.
Proof.
  move=> /[swap]->.
  have: (indom (label (Lab l (single x tt))) (Lab l x)).
  { by rewrite label_single indom_single_eq. }
  exact/disjoint_inv_not_indom_both/fset_htrm_label_remove_disj.
Qed.

Declare Scope fset_scope.
Delimit Scope fset_scope with fs.
Declare Scope fs_hts.
Delimit Scope fs_hts with fh.

Declare Scope fun_scope.
Delimit Scope fun_scope with fn.

Notation "'⟨' l ',' x '⟩'" := (label (Lab l%Z x%fs)) (at level 5, right associativity, format "⟨ l ,  x ⟩").

Definition ntriple H fs_hts Q := H ==> nwp fs_hts Q.

Local Notation hhprop := (hhprop HD).

Lemma xfocus_lemma (l : labType) fs_hts (Q : (HD -> val) -> hhprop) H : 
  let fs_ht := lookup' fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    H ==> wp ⟨l, fs⟩ [eta ht]
            (fun hr => nwp (LibLabType.remove fs_hts l) (fun hr' => Q (hr \u_⟨l, fs⟩ hr'))) ->
    ntriple H fs_hts Q.
Proof.
  move=> fs_ht fs ht.
  rewrite (@wp_ht_eq HD ⟨l, fs⟩ _ (ht_of (el (lookup fs_hts l)))).
  { apply: himpl_trans_r.
    rewrite /nwp (fset_htrm_lookup_remove l fs_hts) -wp_union -/fs_ht; first last.
    { exact/fset_htrm_label_remove_disj. }
    under (wp_ht_eq (htrm_of fs_hts))=> ? IN.
    { rewrite (lookup_eq _ _ IN); over. }
    rewrite -/fs_ht -/ht.
    apply/wp_conseq=> hv.
    under (wp_ht_eq (htrm_of fs_hts))=> ? IN.
    { rewrite (remove_eq _ _ IN); over. }
    move=> h Hwp; rewrite -/fs //. }
  case=> ?? /[! @indom_label_eq]-[<-].
  rewrite /fs/ht/fs_ht/lookup/lookup'/= fset_of''E.
  exact/htrm_of''E.
Qed.

Lemma disjoint_eq_label {T} (l : labType) (fs1 fs2 : fset T) : 
  disjoint (label (Lab l fs1)) (label (Lab l fs2)) <-> disjoint fs1 fs2.
Proof.
  split.
  { move/(@disjoint_inv_not_indom_both _ _ _ _ _)=> dj.
    apply/disjoint_of_not_indom_both=> x in1 in2.
    by apply/(dj (Lab l x)); rewrite indom_label_eq. }
  move/(@disjoint_inv_not_indom_both _ _ _ _ _)=> dj.
  apply/disjoint_of_not_indom_both=> -[??].
  by rewrite ?indom_label_eq=> -[_]/[swap]-[_]/dj/[apply].
Qed.

Lemma disjoint_subset {A} (fs1 fs2 fs : fset A) : 
  disjoint fs1 fs2 -> 
  (forall x, indom fs x -> indom fs1 x) -> 
  disjoint fs fs2.
Proof.
  move/(@disjoint_inv_not_indom_both _ _ _ _ _)=> dj ind.
  apply/disjoint_of_not_indom_both=> ? /ind; eauto.
Qed.

Arguments disjoint_subset {_} _.

Lemma xfocus_pred_lemma (p : D -> Prop) (l : labType) fs_hts (Q : (HD -> val) -> hhprop) H : 
  let fs_ht := lookup' fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    H ==> wp ⟨l, fs ∖ p⟩ [eta ht]
            (fun hr => nwp (Lab l (FH (fs ∩ p) ht) :: LibLabType.remove fs_hts l) (fun hr' => Q (hr \u_⟨l, fs ∖ p⟩ hr'))) ->
    ntriple H fs_hts Q.
Proof.
  move=> fs_ht fs ht.
  have sb: forall x P, indom ⟨l, intr fs P⟩ x -> indom ⟨l, fs⟩ x.
  { case=> ???; by rewrite ?indom_label_eq intr_indom_both=> -[->][]. }
  rewrite (@wp_ht_eq HD _ _ (ht_of (el (lookup fs_hts l)))).
  { apply: himpl_trans_r.
    rewrite /nwp (fset_htrm_lookup_remove l fs_hts) -/fs_ht -/fs. 
    rewrite fset_of_cons /fs_of /=.
    rewrite (wp_ht_eq (fun _ => htrm_of' _ _) (htrm_of fs_hts)).
    { set (Fs := (⟨_,_⟩ \u _)).
      set (Fn := (fun ld => If _ then _ else _)).
      have->: wp Fs Fn = wp Fs (htrm_of fs_hts).
      { apply/fun_ext_1=> ?; apply/wp_ht_eq.
        rewrite /Fs/Fn=> -[l' x] /=.
        case: classicT.
        { case=><- IN ?; rewrite /ht /fs_ht (lookup_eq l) //.
          { rewrite /lookup/lookup' /=.
            rewrite htrm_of''E // -fset_of''E.
            move: IN; rewrite /fs /fs_ht /lookup' /=.
            rewrite intr_indom_both; autos*. }
          apply/sb; rewrite indom_label_eq; eauto. }
        rewrite indom_union_eq=> /[swap]-[].
        { by rewrite indom_label_eq=> -[->]?[]. }
        by move/remove_eq->. }
      rewrite wp_union.
      { rewrite /Fs -union_assoc -label_union.
        rewrite [(_ ∖ _) \u _]union_comm_of_disjoint ?fs_pred_part //.
        rewrite disjoint_comm; exact/fs_pred_part_disj. }
      rewrite /Fs disjoint_union_eq_r disjoint_eq_label; split.
      { rewrite disjoint_comm; exact/fs_pred_part_disj. }
      apply/(disjoint_subset ⟨l, fs⟩); eauto.
      exact/fset_htrm_label_remove_disj. }
    by move=> ? /sb/lookup_eq ->. }
  case=>l' d  /sb; rewrite indom_label_eq=> -[<-]?. 
  by rewrite /ht/lookup/fs_ht/lookup' /= htrm_of''E // -fset_of''E.
Qed.

Definition uni_pred {A B} (f g : A -> B) (p : A -> Prop) := 
  fun x => If p x then f x else g x.

Lemma xfocus_pred_lemma' (p : D -> Prop) (l : labType) fs_hts (Q : (HD -> val) -> hhprop) H : 
  let fs_ht := lookup' fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    H ==> wp ⟨l, fs ∖ p⟩ [eta ht]
            (fun hr => 
              nwp (Lab l (FH (fs ∩ p) ht) :: LibLabType.remove fs_hts l) 
                (fun hr' => Q (lab_fun_upd (uni_pred hr' hr p) hr' l))) ->
    ntriple H fs_hts Q.
Proof.
  move=> fs_ht fs ht Impl.
  apply/(@xfocus_pred_lemma p l). rewrite -/fs_ht -/fs -/ht.
  apply: himpl_trans; eauto. apply/wp_conseq=> hr.
  apply: himpl_trans; first last.
  { apply/wp_hv. } 
  rewrite -/(nwp _ _); apply/wp_conseq=> hr'.
  xsimpl (lab_fun_upd (uni_pred hr' hr p) hr' l)=> ?.
  apply:applys_eq_init; fequals; extens=> -[l' x].
  case: (classicT (l' = l))=>[->|?].
  { rewrite /uni_pred /= /lab_fun_upd /= eqbxx.
    case: classicT=> px.
    { rewrite uni_nin.
      { rewrite /uni; do ? case: classicT=> //=.
        by rewrite eqbxx. }
      rewrite indom_label_eq intr_indom_both /=. autos*. }
    rewrite /uni; case: classicT=> // ?.
    case: classicT=> //=.
    { rewrite indom_union_eq indom_label_eq intr_indom_both=> -[]; autos*.
      by move/indom_remove. }
    rewrite ?eqbxx; by case: classicT. }
  rewrite lab_fun_upd_neq; eauto.
  rewrite /uni; case: classicT=> [/indom_label?|]; first by subst.
  case: classicT=> //; rewrite lab_fun_upd_neq //.
Qed.


Arguments htrm_of : simpl never.

Lemma xunfocus_lemma (Q : (HD -> val) (*-> (HD -> val)*) -> hhprop) fs_hts 
  (ht : D -> trm) (fs : fset D) H (ht' : HD -> _)
  (Q' : (HD -> val) -> (HD -> val) -> hhprop)
  (l : labType) :
  ~ has_lab fs_hts l ->
  (ht = (fun d => ht' (Lab l d))) ->
  (forall hr hr', Q' hr hr' = Q (hr \u_⟨l, fs⟩ hr')) ->
  (* adequate (fun hr => Q hr hr) (⟨l, fs⟩ \u fset_of fs_hts) -> *)
  ntriple H ((Lab l (FH fs ht)) :: fs_hts) (fun hr => Q hr) ->
  H ==> wp ⟨l, fs⟩ ht' (fun hr => nwp fs_hts (fun hr' => Q' hr hr')).
Proof.
  rewrite /ntriple/nwp=> /hasnt_lab /[dup]rE {1}-> /[! fset_of_cons] htE QE.
  apply: himpl_trans_r.
  rewrite -wp_union /=; first last.
  {  exact/fset_htrm_label_remove_disj. }
  under wp_ht_eq=> -[l' d] IN.
  { unfold label in IN. rewrite -> indom_Union in IN. 
    setoid_rewrite -> indom_single_eq in IN.
    simpl in IN.
    destruct IN as (? & ? & IN). injection IN as <-. subst.
    rewrite (@lookup_eq l) rE ?lookup_cons // ?lookup_cons_ht ?lookup_cons_fs //=. 
    { rewrite rE. over. }
    unfold label. rewrite -> indom_Union. eauto. } 
  move=> /= h Hwp; simpl; apply/wp_conseq; eauto=> hr /=; simpl.
  under wp_ht_eq=> ? IN.
  { rewrite (@remove_eq l) /= eqbxx /= // -rE; over. }
  rewrite -rE // => {Hwp}h Hwp.
  eapply wp_conseq; last exact/Hwp.
  by move=> ??; rewrite QE.
Qed.

Lemma nwp0 Q : 
  nwp nil (fun=> Q) = Q.
Proof. by rewrite /nwp fset_of_nil wp0. Qed.

Lemma xcleanup_lemma fs_hts Q v l fs H Q' : 
  ~ has_lab fs_hts l ->
  (forall hr, Q' hr = Q (v \u_⟨l, fs⟩ hr)) ->
  ntriple H fs_hts (fun hr => Q (lab_fun_upd v hr l)) -> 
  H ==> nwp fs_hts (fun hr => Q' hr).
Proof.
  move=> /hasnt_lab-> QE.
  apply: himpl_trans_r; rewrite /nwp.
  move=> ? Hwp; apply/wp_hv; apply: wp_conseq Hwp=> hr ? Qh.
  exists (lab_fun_upd v hr l); rewrite QE.
  move: Qh; apply: applys_eq_init; fequals; apply/fun_ext_1=> -[l' ?].
  rewrite /uni; case: classicT=> [/indom_label->|].
  { by rewrite /lab_fun_upd eqbxx. }
  case: classicT=> // /indom_remove *. 
  rewrite lab_fun_upd_neq //.
Qed.

Lemma hbig_fset_label_single' {DD A} (Q : DD -> LibSepReference.hhprop A) (d : DD) :
  \*_(d0 <- single d tt) Q d0 = Q d.
Proof using.
  unfold hbig_fset.
  rewrite -> update_empty. rewrite -> (snd (@fset_foldE _ _ _ _)); auto.
  2: intros; xsimpl.
  rewrite -> (fst (@fset_foldE _ _ _ _)); auto.
Qed.

Lemma hstar_fset_Lab (Q : labeled D -> hhprop) l fs : 
  \*_(d <- ⟨l, fs⟩) Q d = 
  \*_(d <- fs) (Q (Lab l d)).
Proof.
  elim/fset_ind: fs. 
  { by rewrite label_empty ?hbig_fset_empty. }
  move=> fs x IHfs ?.
  rewrite label_update ?hbig_fset_update // ?indom_label_eq ?IHfs//.
  by case.
Qed.
Hint Rewrite @hbig_fset_label_single' @hstar_fset_Lab : hstar_fset.


Lemma lhtriple_ref : forall (f : val)  l x, 
  htriple ⟨l, (single x tt)⟩ (fun d => val_ref f)
    (\[] : hhprop)
    (fun hr => (\exists (p : loc), \[hr = fun=> val_loc p] \*  p ~(Lab l x)~> f)).
Proof using.
move=> ? l d. rewrite -wp_equiv; apply:himpl_trans; last apply/wp_hv.
simpl; rewrite wp_equiv; apply/htriple_conseq; first apply/htriple_ref. 
{ xsimpl*. }
move=> ?. xpull=> p->. 
xsimpl ((fun=> val_loc (p (Lab l d))) : HD -> _) (p (Lab l d)).
extens=> -[]??; rewrite /uni; case: classicT=> //.
by rewrite indom_label_eq indom_single_eq=> -[]<-<-.
Qed.

Lemma lhtriple_get : forall v (p : loc) fs,
  @htriple D fs (fun d => val_get p)
    (\*_(d <- fs) p ~(d)~> v)
    (fun hr => \[hr = fun => v] \* (\*_(d <- fs) p ~(d)~> v)).
Proof using.
  intros. unfold htriple. intros H'. applys @hhoare_conseq @hhoare_get; xsimpl~.
Qed.

Lemma lhtriple_set : forall v (w : _ -> val) (p : loc) fs,
  @htriple D fs (fun d => val_set p (w d))
  (\*_(d <- fs) p ~(d)~> v)
  (fun hr => \[hr = fun=> val_unit] \* (\*_(d <- fs) p ~(d)~> w d)).
Proof using.
intros. unfold htriple. intros H'. applys @hhoare_conseq @hhoare_set; xsimpl*.
Qed.

Lemma lhtriple_free : forall (p : loc) (v : val) fs,
  @htriple D fs (fun d => val_free p)
    (\*_(d <- fs) p ~(d)~> v)
    (fun _ => \[]).
Proof using. intros. apply htriple_free. Qed.

Hint Resolve (*htriple_ref_lab*) lhtriple_ref lhtriple_get lhtriple_set lhtriple_free : lhtriple.

Arguments xfocus_lemma _ {_}.
Arguments xunfocus_lemma _ {_}.

Lemma xnwp0_lemma H Q :
  H ==> Q ->
  ntriple H nil (fun=> Q).
Proof.
  by apply: himpl_trans_r=> ? /[! nwp0].
Qed.

Lemma xnwp1_lemma fs_ht l :
  wp (label (Lab l (fs_of fs_ht))) (ht_of fs_ht) =
  nwp ((Lab l fs_ht) :: nil).
Proof.
  apply/fun_ext_1=> ?.
  rewrite /nwp /= union_empty_r /htrm_of /=.
  erewrite wp_ht_eq; first eauto.
  case=> ??; rewrite indom_label_eq=> -[<-] /=.
  case: classicT; autos*.
Qed.

Lemma xntriple1_lemma H Q fs_ht l :
  H ==> wp (label (Lab l (fs_of fs_ht))) (ht_of fs_ht) Q =
  ntriple H ((Lab l fs_ht) :: nil) Q.
Proof. by rewrite /ntriple xnwp1_lemma. Qed.

Lemma nwp_of_ntriple H Q fs_hts :
  ntriple H fs_hts Q =
  H ==> nwp fs_hts Q.
Proof. by []. Qed.

Lemma ntriple_conseq_frame H2 H1 H Q fs_ht:
  ntriple H1 fs_ht (Q \*+ \Top) ->
  H ==> H1 \* H2 -> ntriple H fs_ht (Q \*+ \Top).
  move=> T Impl; rewrite /ntriple/nwp wp_equiv.
  apply/htriple_conseq_frame; eauto.
  { rewrite* <-@wp_equiv. }
  xsimpl*.
Qed.

Lemma ntriple_conseq_frame2 H2 H1 Q1 H Q fs_ht : 
  ntriple H1 fs_ht Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q -> ntriple H fs_ht Q.
Proof.
  rewrite /ntriple /nwp ?wp_equiv=> *.
  apply/htriple_conseq_frame; eauto.
Qed.

Lemma ntriple_conseq H1 Q1 H Q fs_ht : 
  ntriple H1 fs_ht Q1 ->
  H ==> H1 ->
  Q1 ===> Q -> ntriple H fs_ht Q.
Proof.
  rewrite /ntriple /nwp ?wp_equiv=> *.
  apply/htriple_conseq; eauto.
Qed.

Lemma ntriple_frame X H Q fs_ht H' Q' : 
  (H = H' X) ->
  (forall v, Q v = Q' X v) ->
  (H' X ==> (H' hempty) \* X) ->
  ((Q' \[]) \*+ X ===> Q' X) ->
  H' \[] ==> nwp fs_ht (fun v => Q' \[] v) ->
  ntriple H fs_ht Q.
Proof.
move=>-> QE ? QI ?.
apply/ntriple_conseq_frame2; eauto=> hv; rewrite* QE.
Qed.

Fact hstar0E : hstar \[] = @id hhprop.
Proof. apply/fun_ext_1=>?. by rewrite hstar_hempty_l. Qed.

Lemma hstar_fset_label_single {A : Type} (x : A) : 
@hbig_fset D _ hstar (single x tt) = @^~ x.
Proof. 
  apply/fun_ext_1=> ?.
  rewrite update_empty hbig_fset_update // hbig_fset_empty. xsimpl*. 
Qed.
Fact hstar_interval_offset (L R offset : int) (f : int -> hhprop) :
  \*_(d <- interval L R) f (d + offset) = 
  \*_(d <- interval (L + offset) (R + offset)) f d.
Proof.
  rewrite <- interval_fsubst_offset.
  rewrite <- hstar_fset_eq with (g:=fun i => i - offset); try reflexivity.
  hnf. intros. lia.
Qed.


End I_didnt_come_up_with_a_name.

Declare Scope fset_scope.
Delimit Scope fset_scope with fs.
Declare Scope fs_hts.
Delimit Scope fs_hts with fh.

Declare Scope fun_scope.
Delimit Scope fun_scope with fn.

Notation "'⟨' l ',' x '⟩'" := (label (Lab l%Z x%fs)) (at level 5, right associativity, format "⟨ l ,  x ⟩").

Arguments disjoint_subset {_} _.

Arguments htrm_of : simpl never.

Hint Resolve (*htriple_ref_lab*) lhtriple_ref lhtriple_get lhtriple_set lhtriple_free : lhtriple.

Arguments xfocus_lemma _ {_}.
Arguments xunfocus_lemma _ {_}.

Notation "'N-WP' fs_hts '{{' v ',' Q '}}'" := 
    (nwp 
      fs_hts%fh
      (fun v => Q%fn)) (at level 20, v name,
      format "'N-WP'  '[' fs_hts '/'  '{{'  v ','  Q  '}}' ']' ") 
    : wp_scope.

Notation "'{{' H '}}' fs_hts '{{' v ',' Q '}}'" := 
    (ntriple 
      H%fn
      fs_hts%fh
      (fun v => Q%fn)) (at level 20, v name,
      format " '[' '[' '{{'  H  '}}' ']' '/   ' '[' fs_hts ']' '/' '[' '{{'  v ','  Q  '}}' ']' ']' ") 
    : wp_scope.

Notation "'[{' fs1 ';' fs2 ';' .. ';' fsn '}]'" := 
  (cons fs1%fh (cons fs2%fh .. (cons fsn%fh nil) ..)) (at level 30
  , format "[{ '['  fs1 ';' '//'  fs2 ';' '//'  .. ';' '//'  fsn  ']' }] "
  ) : fs_hts.

Notation "'[{' fs '}]'" := 
  (cons fs%fh nil) (at level 30, format "[{  fs  }]") : fs_hts.

Export ProgramSyntax.

Notation "'[' l '|' d 'in' fs '=>' t ]" := (Lab (l,0)%Z (FH fs%fs (fun d => t))) 
  (at level 20, t custom trm at level 100, d name) : fs_hts.

Notation "'{' l '|' d 'in' fs '=>' t }" := (Lab (l,0)%Z (FH fs%fs (fun d => t))) 
  (at level 20, d name, only parsing) : fs_hts.

Tactic Notation "xfocus" constr(S) := 
  let n := constr:(S) in
  apply (@xfocus_lemma _ n); simpl; try apply xnwp0_lemma.

Tactic Notation "xfocus" constr(S) constr(P) := 
  let n := constr:(S) in
  let P := constr:(P) in
  apply (@xfocus_pred_lemma' _ P (n,0)%Z); simpl; rewrite /uni_pred /=; rewrite -?xntriple1_lemma; try apply xnwp0_lemma.

Tactic Notation "xfocus_split_core" constr(HPP) constr(S) constr(P) :=
  repeat match HPP with
  | context[hbig_fset _ ?ffs ?ff] =>
    match ffs with
    | context[intr _ _] => fail
    | _ =>
      match ff with
      | context[Lab (S,0)%Z] => rewrite -> (fun_eq_1 ff (hbig_fset_part ffs P)) in |- *
      end
    end
  end.

Tactic Notation "xfocus_split" constr(S) constr(P) :=
  match goal with
  | |- (?HPP ==> _) => xfocus_split_core HPP S P
  | |- (ntriple ?HPP _ _) => xfocus_split_core HPP S P
  end.

Tactic Notation "xfocus" "*" constr(S) constr(P) := 
  xfocus S P; xfocus_split S P.

Tactic Notation "xframe" constr(H) := 
  let h := constr:(H) in
  eapply (@ntriple_conseq_frame _ h (protect _)); [|xsimpl]; rewrite /protect; eauto.

Tactic Notation "xunfocus" := 
eapply xunfocus_lemma=> //=; [intros; remember ((_ \u_ _) _); reflexivity|]=>/=.

Tactic Notation "xcleanup" constr(n) := 
match goal with 
| |- context G [?v \u_ ⟨_, ?fs⟩] => eapply ((@xcleanup_lemma _ _ _ v (n,0)%Z fs))
end=>//; [intros; remember ((_ \u_ _) _); reflexivity|].


Tactic Notation "xin" constr(S1) ":" tactic(tac) := 
  let n := constr:(S1) in
  xfocus (n, 0)%Z; tac; try(
  first [xunfocus | xcleanup n]; simpl; try apply xnwp0_lemma); rewrite -?xntriple1_lemma /=.


Tactic Notation "xin" constr(S1) constr(S2) ":" tactic(tac) := 
  let n1 := eval vm_compute in (Z.to_nat S1) in
  let n2 := eval vm_compute in (Z.to_nat S2) in
  xfocus n1; tac; first [xunfocus | xcleanup n1];
  xfocus n2; tac; first [xunfocus | xcleanup n2]; simpl; try apply xnwp0_lemma.

Tactic Notation "xnsimpl" := 
  rewrite /ntriple; xsimpl; try first [ setoid_rewrite <-nwp_of_ntriple| rewrite -nwp_of_ntriple].

Notation "f '[`' i '](' j ')'" := (f (Lab (i,0)%Z j)) (at level 30, format "f [` i ]( j )") : fun_scope.
Notation "'⟨' l ',' x '⟩'" := ((Lab l%Z x%fs)) (at level 5, right associativity, format "⟨ l ,  x ⟩") : arr_scope.

Global Hint Rewrite @hstar_fset_label_single @hstar_fset_Lab : hstar_fset.

Arguments lab_fun_upd /.

Global Arguments ntriple_frame _ {_}.

Tactic Notation "xframe2" uconstr(QH) := 
  (try (xframe QH; [ ]));
  try (
    let Q := fresh "Q" in 
    let HEQ := fresh "Q" in 
    remember QH as Q eqn: HEQ in |- *;
    rewrite -?HEQ;
    eapply (@ntriple_frame _ Q); 
    [ let h := fresh "h" in 
      let f := fresh "h" in 
      match goal with |- ?x = ?y => set (h := x) end;
      pattern Q in h;
      set (f := fun _ => _) in h;
      simpl in h;
      rewrite /h;
      reflexivity
    | let h := fresh "h" in 
      let f := fresh "h" in 
      let v := fresh "h" in 
      intros v; 
      match goal with |- ?x = ?y => set (h := x) end;
      pattern Q, v in h;
      set (f := fun _ _ => _) in h;
      simpl in h;
      rewrite /h;
      reflexivity
    | simpl; try rewrite HEQ; xsimpl*
    | simpl=> ?;
      try (have->: forall f, (fun x : hheap _ => f x) = f by []);
      try (have->: forall f, (fun x : hheap D => f x) = f by []);
      try rewrite HEQ;
      xsimpl*
    | simpl; rewrite -> ?hstar0E
    ]; clear Q HEQ
  ).

Tactic Notation "xcleanup_unused" := 
  (repeat let HH := fresh "uselessheap" in set (HH := hbig_fset hstar (_ ∖ _) _); xframe2 HH; clear HH).

Tactic Notation "xcleanup_unused" "*" :=
  rewrite -> ! hbig_fset_hstar; xcleanup_unused; rewrite -!hbig_fset_hstar; xsimpl.

Tactic Notation "xdrain_unused" := 
  (repeat let HH := fresh "uselessheap" in set (HH := hbig_fset hstar (_ ∖ _) _); xframe HH; clear HH).

Tactic Notation "xdrain_unused" "*" :=
  rewrite -> ! hbig_fset_hstar; xdrain_unused; rewrite -!hbig_fset_hstar.

Tactic Notation "xclean_heap_core" constr(Q) :=
  match Q with
  | context[htop] => xdrain_unused
  | _ => try xcleanup_unused
  end.

Tactic Notation "xclean_heap" := 
  match goal with
  | |- (himpl _ (nwp _ ?Q)) => xclean_heap_core Q
  | |- (ntriple _ _ ?Q) => xclean_heap_core Q
  end.

Arguments wp_for _ _ {_}.

Arguments disjoint_inv_not_indom_both {_ _ _ _ _}.

Lemma disjoint_single {T} (x y : T) : 
  disjoint (single x tt) (single y tt) = (x <> y).
Proof.
  extens; split; last apply/disjoint_single_single.
  move/[swap]->; exact/disjoint_single_single_same_inv.
Qed.

Lemma disjoint_interval (x1 y1 x2 y2 : int) : 
  disjoint (interval x1 y1) (interval x2 y2) = ((y1 <= x2) \/ (y2 <= x1) \/ (y1 <= x1) \/ (y2 <= x2)).
Proof.
  extens; split=> [/(@disjoint_inv_not_indom_both _ _ _ _ _)|].
  { setoid_rewrite indom_interval=> /[dup]/(_ x1)+/(_ x2).
   lia. }
  move=> H; apply/disjoint_of_not_indom_both=> ?; rewrite ?indom_interval.
  move: H; lia.
Qed.

Lemma disjoint_single_interval (x1 y1 x : int) : 
  disjoint (single x tt) (interval x1 y1) = ((x < x1) \/ (y1 <= x)).
Proof.
  extens; split=> [/(@disjoint_inv_not_indom_both _ _ _ _ _)|].
  { move=> /[dup]/(_ x); rewrite indom_interval indom_single_eq.
    lia. }
  move=> H; apply/disjoint_single_of_not_indom.
  rewrite indom_interval. math.
Qed.


Lemma disjoint_interval_single (x1 y1 x : int) : 
  disjoint (interval x1 y1) (single x tt) = ((x < x1) \/ (y1 <= x)).
Proof. by rewrite disjoint_comm disjoint_single_interval. Qed.

Lemma disjoint_label {T} (l l' : labType) (fs1 fs2 : fset T) : 
  disjoint (label (Lab l fs1)) (label (Lab l' fs2)) = ((l <> l') \/ disjoint fs1 fs2).
Proof.
  extens; split=> [/(@disjoint_inv_not_indom_both _ _ _ _ _)|].
  { move=> IN; case: (classicT (l = l')); [right|left]=> //; subst.
    apply/disjoint_of_not_indom_both=> x.
    move: (IN (Lab l' x)); rewrite ?indom_label_eq; autos*. }
  case: (classicT (l = l'))=> [<-|? _].
  { rewrite*  @disjoint_eq_label. }
  apply/disjoint_of_not_indom_both=> -[??]; rewrite ?indom_label_eq.
  case=><-; autos*.
Qed.

Lemma disjoint_prod {A B : Type} (fs1 fs2 : fset A) (fr1 fr2 : fset B): 
  disjoint (fs1 \x fr1) (fs2 \x fr2) = (disjoint fs1 fs2 \/ disjoint fr1 fr2).
Proof.
  extens; splits.
  { move/disjoint_inv_not_indom_both=> Dj.
    case: (prop_inv (disjoint fs1 fs2)); autos*.
    move=> NDj; right; apply/disjoint_of_not_indom_both=> x ??.
    have: ~ (forall p : A, indom (fs1) p -> indom (fs2) p -> False).
    { by move=> ?; apply/NDj/disjoint_of_not_indom_both. }
    rewrite not_forall_eq=> -[]y IN.
    apply/(Dj (y,x)); rewrite indom_prod=> /=; splits=>//.
    all: apply:not_not_inv=> ?; apply/IN; autos*. }
  case=> /disjoint_inv_not_indom_both=> Dj.
  all: apply/disjoint_of_not_indom_both=> -[]??; rewrite ?indom_prod/=; autos*.
Qed.

Global Hint Rewrite @disjoint_single disjoint_interval disjoint_single_interval 
  disjoint_interval_single @disjoint_eq_label @disjoint_label @disjoint_prod : disjointE.

Global Hint Rewrite @indom_label_eq @indom_union_eq @indom_prod @indom_interval @indom_single_eq @intr_indom @intr_neg_indom @indom_Union : indomE.

Ltac indomE := autorewrite with indomE.

Ltac disjointE := 
  let Neq := fresh in
  let i   := fresh "i" in
  let j   := fresh "j" in 
  try intros i j; 
  indomE;
  autorewrite with disjointE; try lia; try eqsolve.

Definition Get {A} Z N (fsi : int -> fset A) (x : A)  :=
  match classicT (exists i, indom (interval Z N) i /\ indom (fsi i) x) with 
  | left P => 
    let '(@exist _ _ a _) := indefinite_description P in a
  | _ => 0
  end.

Lemma Get_in {A} Z N i x (fsi : int -> fset A) : 
  Z <= i < N ->
  indom (fsi i) x ->
    indom (fsi (Get Z N fsi x)) x /\ 
    indom (interval Z N) (Get Z N fsi x).
Proof.
  move=> ??; rewrite /Get; case: classicT=> [?|[] ].
  { case: (indefinite_description _)=> j [] ? //. }
  by exists i; rewrite indom_interval.
Qed.

Definition set2 D y : labeled D -> labeled D :=
  fun '(Lab (p, q) x) => Lab (p, y) x.

Arguments el {_}.

Lemma xfor_lemma D `{ID : Inhab (labeled D)}
  Inv 
  (R R' : D -> hhprop (labeled D))
  m vd (H : int -> hhprop (labeled D)) (H' : int -> (labeled D -> val) -> hhprop(labeled D) )
  s fsi1 vr
  (N: Z) (C1 : D -> trm) (C : trm)
  (i j : Z)
  Pre Post: 
  (forall (l : int) Q, 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R (el d)) \* 
        Q \(m, vd) H l }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R' (el d)) \* 
        Q \(m, vd) H' l v }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall j : int, hlocal (H j) ⟨(i,0%Z), single s tt⟩) ->
  (forall (j : int) (v : labeled D -> val), hlocal (H' j v) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : D, hlocal (R i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : D, hlocal (R' i) ⟨(j,0%Z), single i tt⟩) ->
  (forall (hv hv' : labeled D -> val) (m : int),
    (0 <= m < N) ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    H' m hv = H' m hv') ->
  comm m -> assoc m ->
  (forall x y, (vd x /\ vd y) <-> vd (m x y)) ->
  (i <> j)%Z ->
  0 <= N ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union (interval 0 N) fsi1) R d) \*
    \(m, vd)_(i <- interval 0 N) H i) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union (interval 0 N) fsi1) R' d) \* 
    (\(m, vd)_(i <- interval 0 N) H' i hv) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For 0 N (trm_fun vr C)};
      {j| ld in Union (interval 0 N) fsi1 => C1 ld}
    }]
  {{ v, Post v }}.
Proof.
  move=> IH lI lH lH' lR lR' opP CM AS VM iNj N0 ? ??? ?? PreH PostH.
  rewrite /ntriple /nwp ?fset_of_cons /= union_empty_r.
  set (f := (fun '(Lab (p, q) x) => Lab 
    (If p = j then 
      If  0 <= q < N /\ indom (fsi1 q) x then (j,0)%Z else (p, 2 * (q + N) + 1)
    else (p, q)) 
    x) : labeled D -> labeled D).
  set (g := (fun '(Lab (p, q) x) => Lab 
    (If p = j then 
      If q = 0 /\ indom (Union (interval 0 N) fsi1) x then
        (j, Get 0 N fsi1 x)
      else (j, -1)
    else (p, q)) x)).
  set (fi (i : int) := (fun '(Lab (p, q) x) => If p = j then Lab (j, q - i) x else Lab (p, q) x) : labeled D -> labeled D).
  set (gi (i : int) := (fun '(Lab (p, q) x) => If p = j then Lab (j, q + i) x else Lab (p, q) x) : labeled D -> labeled D).
  set (fsi' (i : int) := ⟨(j, i), fsi1 i⟩).
  have H'E :forall hv, 
    \(m, vd)_(i <- interval 0 N) H' i hv = \(m, vd)_(i <- interval 0 N) H' i (hv \o f \o set2 i).
  { move=> hv; apply/hbig_fset_eq=> d. rewrite indom_interval=> ?.
    apply/opP=> // x ? /=; case: classicT=> // _.
    by case: classicT=> // -[]; split=> //. }
  set (r := fun x => if lab_eqb (lab x) (j,0) then R (el x) else \[]).
  set (r' := fun x => if lab_eqb (lab x) (j,0) then R' (el x) else \[]).
  apply/(
    wp_for_hbig_op_na_bis Inv (r) (r') H (fun i hv => H' i (hv \o set2 i))  
      (fun d => ⟨(j,0%Z), fsi1 d⟩) Post fsi' fi gi g
      (fs' := ⟨(i, 0), single s tt⟩)
      (f := f)
      (* (fsi' := fsi') *)
  ); try eassumption.
  { rewrite -Union_label /r/r' . xsimpl*; rewrite eqbxx //. }
  { by rewrite -Union_label. }
  { by case=> l d; rewrite indom_label_eq /= /htrm_of; case: classicT. }
  { by move=> *. }
  { case=> [??]; rewrite /r; case: ssrbool.ifP=> // [|?]. 
    { by move=> /= /lab_eqbP->; rewrite -label_single. }
    exact/hlocal_hempty. }
  { case=> [??]; rewrite /r'; case: ssrbool.ifP=> // [|?]. 
    { by move=> /= /lab_eqbP->; rewrite -label_single. }
    exact/hlocal_hempty. }
  { clear. move=> ? [][??]?; rewrite /gi /fi.
    (do ? case: classicT=> //)=>_->; do ? fequals; lia. }
  { clear. move=> ? [][??]?; rewrite /gi /fi.
    (do ? case: classicT=> //)=>_->; do ? fequals; lia. }
  { clear. move=> i; rewrite /fi /fsi'; clear.
    apply/fset_extens=> -[][] l1 l2 x.
    rewrite indom_fsubst; split; rewrite ?indom_label_eq.
    { case=> -[][]m1 m2 y; rewrite indom_label_eq.
      case: classicT=> [->|/[swap] ] [][]-><-->[][]-> //; split=> //.
      fequals; lia. }
    case=> -[]-><- ?.
    exists (Lab (l1, i) x); case: classicT=> //; rewrite indom_label_eq.
    (do ? split); do ? fequals; lia. }
  { rewrite /fsi' /f /fi; clear -iNj. move=> ? [][]l1 l2 x; rewrite indom_label_eq.
    rewrite indom_interval=> /[swap]; case=> -[]->->??.
    case: classicT=> // ?.
    case: classicT=> // [|[] ] // _.
    do ? fequals; lia. }
  { rewrite /f /fsi' /Fs; clear -N0 iNj=> -[][]l1 l2 x[][]m1 m2 y ?.
    do ? case:classicT=> //.
    { case=> ??->[]??->[]?. rewrite ?indom_Union.
      split; [exists l2|exists m2]; by rewrite indom_interval indom_label_eq. }
    all: try (move=> ???? []; lia).
    all: try (move=> ??? []?; by subst).
    move=> ???? [] *; have?: l2 = m2 by (lia). by subst. }
  { case=> -[]l1 l2 x; clear -iNj.
    split.
    { rewrite indom_fsubst=> -[][][]m1 m2 y[] /[swap].
      rewrite indom_union_eq=> -[].
      { rewrite indom_label_eq indom_single_eq=> -[][]<-<-<-.
        rewrite /f; case: classicT=> // ? []<-<-<-.
        rewrite /g; case: classicT=> // _.
        rewrite indom_union_eq indom_label_eq indom_single_eq; by left. }
      rewrite /Fs indom_Union /fsi' => -[k][]; rewrite indom_label_eq indom_interval=> I [][].
      move=> <- <- ind; rewrite /f; case: classicT=> //.
      case: classicT=> [|[] ] // _ _ []<-<-<-.
      rewrite indom_union_eq; right.
      rewrite /g; case: classicT=> //.
      case: classicT.
      { move=> _ _; rewrite indom_Union; exists (Get 0 N fsi1 y).
        rewrite indom_label_eq.
        by case: (Get_in _ I ind); do ? split. }
      case; split=> //; rewrite indom_Union; exists k.
      split=> //; by rewrite indom_interval. }
    rewrite indom_union_eq=> -[].
    { rewrite /g; (do ? case: classicT)=> [??|??|]; rewrite indom_label_eq.
      1,2: by move=> -[][]/iNj.
      move=> ? [][]<-<- ?.
      rewrite indom_fsubst; exists (⟨(i, 0), x⟩)%arr; split.
      { by rewrite /f; case: classicT. }
      by rewrite indom_union_eq; left; rewrite indom_label_eq. }
    rewrite /Fs indom_Union=> -[]k[]/[dup]?.
    rewrite indom_interval=> ?.
    rewrite /fsi'/ g; case: classicT=> [->|].
    {  case: classicT.
        { case=> -> ?; rewrite indom_label_eq=> -[][]??.
          rewrite indom_fsubst; exists (Lab (j, k) x); split.
          { rewrite /f; case: classicT=> // _.
            case: classicT=> // -[] //. }
          rewrite indom_union_eq indom_Union; right.
          exists k; by rewrite indom_label_eq. }
        move=> _; rewrite indom_label_eq=> -[][]. lia. }
      move=> ?; rewrite indom_label_eq=> -[][]. lia. }
    { case=> -[]l1 l2 x; clear -iNj.
      rewrite indom_union_eq=> -[]; rewrite indom_label_eq=> -[][]<-<-.
      { move=> ?; rewrite /f /g; do ? case: classicT=> //. }
      move=> /[dup] ?.
      rewrite indom_Union=> -[]k[]/[dup]?.
      rewrite indom_interval /g=> ??.
      case: classicT=> // _; case: classicT=> [|[]//] _.
      rewrite /f; case: classicT=> //=> _.
      case: classicT=> // -[].
      case: (@Get_in _ 0 N k x fsi1)=> //.
      rewrite indom_interval //. }
    { rewrite /f; clear -iNj.
      case=> -[]l1 l2 x. rewrite ?indom_label_eq indom_single_eq=> -[][]<-<-<-.
      by case: classicT. }
    { rewrite /gi; clear -iNj.
      case=> [][]l1 l2 x ?; rewrite indom_label_eq indom_single_eq.
      case=> -[]<-<- <-; case: classicT=> //. }
    { rewrite /fsi'=> ? _; clear -iNj.
      apply/disjoint_of_not_indom_both=> -[][]???.
      by rewrite ?indom_label_eq=> -[][]<- _ _ [][]/iNj. }
    { rewrite /fsi'=> ? _; clear -iNj.
      apply/disjoint_of_not_indom_both=> -[][]???.
      by rewrite ?indom_label_eq=> -[][]<- _ _ [][]/iNj. }
    { move=> ??; rewrite /fsi'; clear=> ?.
      apply/disjoint_of_not_indom_both=> -[][]???.
      rewrite ?indom_label_eq=> -[][]_ <-_[][]_ ?; by subst. }
    { move=> ?; rewrite -Union_label hstar_fset_Lab/= -H'E.
      rewrite /r' /= eqbxx; apply/PostH. }
    { move=> > ? hvP. apply/opP=> // * /=. apply/hvP.
      by rewrite indom_label_eq. }
    move=> l Q ?; move: (IH l Q).
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
    rewrite union_empty_r => {}IH.
    have->: 
      (fun hr : labeled D -> val => Inv (l + 1) \* (\*_(d <- ⟨(j, 0), fsi1 l⟩) r' d) \* Q \(m, vd) H' l ((hr \o f) \o set2 l)) = 
      (fun hr : labeled D -> val => Inv (l + 1) \* (\*_(d <- ⟨(j, 0), fsi1 l⟩) R' (el d)) \* Q \(m, vd) H' l hr).
    { apply/fun_ext_1=> ?; do 2? fequals.
      { by xsimpl; rewrite /r' /= eqbxx. }
      f_equal.
      apply/opP=> // x ? /=; case: classicT=> // _.
      case: classicT=> // -[]; split=> //; lia. }
    rewrite /r hstar_fset_Lab {1}/lab eqbxx -(hstar_fset_Lab (fun d => R(el d))).
    erewrite wp_ht_eq; first (apply/IH; lia).
    case=> l' ?; rewrite indom_union_eq ?indom_label_eq=> -[][??]; subst.
    { rewrite uni_in ?indom_label_eq //= /htrm_of.
      case: classicT=> //; autos*. }
    have?: (i, 0) <> (j, 0) by case.
    rewrite uni_nin ?indom_label_eq /= /htrm_of; autos*.
    do ? (case: classicT=> //=; autos* ).
    move=> [_]?[]; split=> //.
    rewrite indom_Union; setoid_rewrite indom_interval; do ? (eexists; eauto).
    all: lia.
Qed.

Hint Resolve eqbxx : lhtriple.