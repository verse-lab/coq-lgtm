Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct.
From SLF Require Import Fun LabType.
From mathcomp Require Import ssreflect ssrfun.
Hint Rewrite conseq_cons' : rew_listx.

Module NatDom : Domain with Definition type := nat.
Definition type := nat.
End NatDom.

Module IntDom : Domain with Definition type := int.
Definition type := int.
End IntDom.

(* auxiliary things *)

Lemma list_from_map {A : Type} `{Inhab A} (f : int -> A) (L : nat) : 
  exists l : list A, length l = L /\
    forall i : int, (0 <= i < L)%Z -> nth (abs i) l = f i.
Proof.
  induction L as [ | L IH ].
  { exists (@nil A). split; auto. intros. math. }
  { destruct IH as (l & HL & HH).
    exists (l ++ (f L :: nil)).
    split. 1: rewrite -> length_last, -> HL; math.
    intros.
    destruct (Z.leb L i) eqn:E.
    { rewrite -> Z.leb_le in E.
      replace (abs i) with L by math.
      rewrite -> nth_last_case. case_if. subst.
      by replace i with (nat_to_Z (length l)) by math.
    }
    { rewrite -> Z.leb_gt in E.
      rewrite -> nth_app_l. 2: math.
      apply HH. math.
    }
  }
Qed.

Module Export AD := WithArray(IntDom).
Check eq_refl : D = labeled int.

Global Instance Inhab_D : Inhab D. 
Proof Build_Inhab (ex_intro (fun=> True) (Lab (0, 0) 0) I).

Definition val_int_add (a b : val) :=
  (match a with val_int a' => a' | _ => 0 end) + 
    (match b with val_int a' => a' | _ => 0 end).

Fact comm_val_int_add : comm val_int_add.
Proof using. 
  clear.
  hnf. intros. unfold val_int_add. destruct x, y; try math; auto.
Qed.

Fact assoc_val_int_add : assoc val_int_add.
Proof using. 
  clear.
  hnf. intros. unfold val_int_add. destruct x, y, z; try math; auto.
Qed.

Lemma val_int_add_distr (a b : int) :
  val_int (a + b) = val_int_add (val_int a) (val_int b).
Proof eq_refl.

Lemma fold_fset_summation_dedicated (N : int) (HN : (0<=N)%Z) (v : D -> val) (l : labType)
  (Larr : list val) (Hlen : length Larr = abs N) 
  (Hcorr : forall d, indom (interval 0 N) d -> v (Lab l d) = nth (abs d) Larr) :
  fset_fold (val_int 0)
      (fun (d : D) (acc : val) =>
      val_int (val_int_add acc (v d))) ⟨l, interval 0 N⟩ =
  fold_left (fun a b : val => val_int (val_int_add a b)) (val_int 0) Larr.
Proof.
  remember (abs N) as n eqn:E.
  revert N E Larr Hlen Hcorr HN.
  induction n as [ | n IH ]; intros.
  { replace N with 0 in * by math.
    rewrite label_empty.
    rewrite -> (fst (@fset_foldE _ _ _ _)); auto.
    apply length_zero_inv in Hlen. subst Larr. by rewrite fold_left_nil.
  }
  { assert (length Larr > 0%nat) as Htmp by math.
    apply length_pos_inv_last in Htmp.
    destruct Htmp as (x & l' & ->).
    rewrite -> fold_left_last.
    replace N with ((N-1)+1) by math.
    rewrite intervalUr; try math.
    rewrite label_update. rewrite -> (snd (@fset_foldE _ _ _ _)); auto.
    2: intros; destruct (v a), (v b); unfold val_int_add; try math.
    2: rewrite indom_label_eq indom_interval; intros ?; math.
    rewrite length_last in Hlen. simpl in Hlen. inversion Hlen.
    rewrite -> IH with (Larr:=l'); try math.
    2:{ intros. rewrite indom_interval in H. rewrite -> Hcorr.
      { rewrite nth_last_case. case_if; try math; auto. }
      { rewrite indom_interval. math. }
    }
    rewrite Hcorr. 2: rewrite indom_interval; math.
    rewrite nth_last_case. case_if; try math.
    by rewrite comm_val_int_add.
  }
Qed. 

Lemma val_int_add_fold_transform hv fs : 
  val_int (fset_fold 0 (fun d : labeled int =>
                Z.add^~ match hv d with
                        | val_int n => n
                        | _ => 0
                        end) fs) =
  fset_fold (val_int 0) (fun (d : labeled int) (acc : val) => val_int_add acc (hv d))
    fs.
Proof.
  pattern fs. apply fset_ind; clear fs.
  { rewrite -> ! (fst (@fset_foldE _ _ _ _)); auto. }
  { intros.
    rewrite -> ! (snd (@fset_foldE _ _ _ _)); auto.
    2: intros; destruct (hv a), (hv b); unfold val_int_add; try math.
    2: intros; destruct (hv a), (hv b); unfold val_int_add; try math.
    rewrite -> val_int_add_distr, -> H. by destruct (hv x).
  }
Qed.

(* why so troublesome? *)

Fact fset_fold_val_int_add_is_int fs (hv : D -> val) v :
  fset_fold (val_int 0) (fun d (acc : val) => val_int (val_int_add acc (hv d))) fs = v ->
  exists x : int, v = val_int x.
Proof.
  revert v. pattern fs. apply fset_ind; clear fs; intros.
  { rewrite -> ! (fst (@fset_foldE _ _ _ _)) in H. eauto. }
  { rewrite -> ! (snd (@fset_foldE _ _ _ _)) in H1.
    3: assumption.
    2: intros; destruct (hv a), (hv b); unfold val_int_add; try math.
    match type of H1 with val_int (val_int_add ?a ?b) = _ => 
      destruct a eqn:E, b eqn:E' end.
    all: unfold val_int_add in H1; simpl in H1; try (by exists 0).
    all: try eauto.
  }
Qed.

Lemma fset_fold_val_int_add_union (fs fs' : fset D) (Hdj : disjoint fs fs') 
  (hv : D -> val) :
  fset_fold (val_int 0) (fun d acc => val_int (val_int_add acc (hv d))) (fs \u fs') =
  val_int (val_int_add 
    (fset_fold (val_int 0) (fun d acc => val_int (val_int_add acc (hv d))) fs)
    (fset_fold (val_int 0) (fun d acc => val_int (val_int_add acc (hv d))) fs')).
Proof.
  revert fs Hdj.
  pattern fs'. apply fset_ind; clear fs'; intros.
  { rewrite -> union_empty_r.
    rewrite -> ! (fst (@fset_foldE _ _ _ _)).
    match goal with |- _ = val_int (val_int_add ?a ?b) => 
      destruct a eqn:E; unfold val_int_add; simpl end.
    all: pose proof E as Htmp; apply fset_fold_val_int_add_is_int in Htmp; 
      destruct Htmp; try discriminate.
    math.
  }
  { rewrite -> union_comm_of_disjoint. 2: apply Hdj.
    rewrite <- update_union_not_r'. 2: constructor; exists tt; apply I.
    rewrite -> ! (snd (@fset_foldE _ _ _ _)).
    2,4: intros; destruct (hv a), (hv b); unfold val_int_add; try math.
    2: assumption.
    2:{ rewrite -> indom_union_eq. 
      rewrite -> disjoint_comm, -> disjoint_update in Hdj.
      eqsolve.
    }
    rewrite -> union_comm_of_disjoint.
    2: rewrite -> disjoint_comm, -> disjoint_update in Hdj; intuition.
    rewrite -> H.
    2: rewrite -> disjoint_comm, -> disjoint_update in Hdj; intuition.
    unfold val_int_add. math.
  }
Qed.

Lemma hcells_form_transform_pre (Z L : int) (HZpos : (0 <= Z)%Z) (HLpos : (0 <= L)%Z) (px : loc) (l : D) (hv : int -> val) 
  (Larr : list val) 
  (Hlen : length Larr = abs L)
  (Hcorr : forall i : int, (0 <= i < abs L)%Z -> nth (abs i) Larr = hv (i + Z)) :
  \*_(d <- interval Z (Z + L)%Z) (px + (abs d))%nat ~(l)~> hv d = 
  hcells Larr (px + (abs Z))%nat l.
Proof.
  remember (abs L) as n eqn:E.
  revert Z L HZpos HLpos px l hv Larr Hlen E Hcorr.
  induction n as [ | n IH ]; intros.
  { replace L with 0 by math.
    rewrite -> intervalgt, -> hbig_fset_empty; try math.
    apply length_zero_inv in Hlen. by subst.
  }
  { rewrite -> intervalU. 2: math.
    rewrite -> hbig_fset_update; auto.
    2: rewrite -> indom_interval; intros ?; math.
    destruct Larr as [ | x Larr ].
    1: rewrite length_nil in Hlen; math.
    simpl.
    f_equal.
    { specialize (Hcorr 0).
      change (abs 0) with 0%nat in Hcorr.
      rewrite -> nth_zero in Hcorr.
      rewrite -> Hcorr; auto; try math.
    }
    { replace (Z + L) with ((Z + 1) + (L - 1)) by math.
      erewrite -> IH with (Z:=Z+1) (L:=L-1) (Larr:=Larr); try math.
      2: rewrite -> length_cons in Hlen; math.
      1: f_equal; math.
      intros.
      specialize (Hcorr (i+1)).
      replace (i + (Z + 1)) with (i + 1 + Z) by math.
      rewrite <- Hcorr; try math.
      replace (abs (i + 1)) with (S (abs i)) by math.
      by rewrite -> nth_cons.
    }
  }
Qed.

Lemma hcells_form_transform (L : int) (HLpos : (0 <= L)%Z) (px : loc) (l : D) (hv : int -> val) 
  (Larr : list val) 
  (Hlen : length Larr = abs L)
  (Hcorr : forall i : int, (0 <= i < abs L)%Z -> nth (abs i) Larr = hv i) :
  \*_(d <- interval 0 L) (px + (abs d))%nat ~(l)~> hv d = 
  hcells Larr px l.
Proof.
  etransitivity. 2: etransitivity. 
  2: apply hcells_form_transform_pre with (Z:=0) (L:=L) (Larr:=Larr) (px:=px) (hv:=hv).
  6: change (abs 0) with 0%nat; rewrite Nat.add_0_r; reflexivity.
  all: try math.
  1: replace (0+L) with L by math; auto.
  intros. replace (i+0) with i by math; auto.
Qed.

Fact hstar_hexists_comm {A : Type} (H : A -> hhprop) H' : 
  (hexists H) \* H' = (hexists (fun a => H a \* H')).
Proof. xsimpl. Qed.

Fact fsubst_indom_local (fs : fset D) (h : hheap D) f : 
  (forall p d, indom (fsubst h f) (p, d) -> indom fs d) -> 
  local fs (fsubst h f).
Proof. intros H. hnf. intros. now apply H in H0. Qed.

Definition Sum (fs : fset int) (f : int -> int) : int :=
  fset_fold 0 (fun idx acc => acc + (f idx)) fs.
Reserved Notation "'Σ_' ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' Σ_ ( i  <-  r ) '/  '  F ']'").

Notation "'Σ_' ( i <- r ) F" :=
  (Sum r (fun i => F)) : nat_scope.

Lemma Sum0 : Sum empty = fun=> 0.
Proof. unfold Sum. extens. intros F. rewrite -> (fst (@fset_foldE _ _ _ _)); auto. Qed.

Lemma SumxSx F x y (H : x <= y) : Sum (interval x (y + 1)) F = Sum (interval x y) F + F y.
Proof.
  unfold Sum. rewrite -> intervalUr. 2: math.
  rewrite -> (snd (@fset_foldE _ _ _ _)); auto. 
  math. rewrite indom_interval; intros ?; math.
Qed.

Lemma SumEq F G (fs : fset int) :
  (forall x, indom fs x -> F x = G x) -> Sum fs F = Sum fs G.
Proof.
  intros.
  revert H. pattern fs. apply fset_ind; clear fs; intros.
  { by rewrite -> Sum0. }
  { unfold Sum.
    rewrite -> ! (snd (@fset_foldE _ _ _ _)); try assumption; try math.
    fold (Sum fs F). fold (Sum fs G).
    rewrite -> H, -> H1. 1: reflexivity.
    1: apply indom_update.
    intros. apply H1. rewrite -> indom_update_eq. by right.
  }
Qed.

(* a specialized conclusion *)
Fact summation_const_for_rlsum (c x y : int) l (H : x <= y) : 
  fset_fold 0 (fun=> Z.add^~ c) (label (Lab l (interval x y))) = 
  c * (y - x).
Proof using.
  remember (abs (y - x)) as n.
  revert x y H Heqn. induction n; intros.
  { assert (x = y) as -> by math.
    rewrite -> intervalgt with (x:=y) (y:=y).
    2: math.
    rewrite label_empty.
    rewrite -> ! (fst (@fset_foldE _ _ _ _)); try math.
  }
  { rewrite -> intervalU. 2: math.
    rewrite label_update. 
    rewrite -> ! (snd (@fset_foldE _ _ _ _)); try math.
    2:{ intros HH. rewrite -> indom_label_eq in HH.
      destruct HH as (_ & HH). rewrite -> indom_interval in HH. math.
    }
    rewrite -> IHn; math.
  }
Qed.

Lemma xfor_big_op_lemma Inv (R R' : IntDom.type -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1 vr
  Z N (C1 : IntDom.type -> trm) (i j : int) (C : trm)
  Pre Post: 
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R d) \* 
       p ~⟨(i, 0%Z), s⟩~> (val_int x) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' d) \* 
        p ~⟨(i, 0%Z), s⟩~> (val_int (x + (op hv l))) }}) ->
  (forall i0 j0 : int, i0 <> j0 -> disjoint (fsi1 i0) (fsi1 j0)) ->
  (forall (hv hv' : D -> val) m,
    (forall i, indom (fsi1 m) i -> hv[j](i) = hv'[j](i)) ->
    op hv m = op hv' m) ->
  (i <> j) ->
  (Z <= N)%Z ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi1) R d) \*
    p ~⟨(i, 0%Z), s⟩~> val_int 0) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi1) R' d) \* 
    p ~⟨(i, 0%Z), s⟩~> val_int (Σ_(i <- interval Z N) (op hv i)) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For Z N (trm_fun vr C)};
      {j| ld in Union (interval Z N) fsi1 => C1 ld}
    }]
  {{ hv, Post hv }}.
Proof.
  move=> IH Dj opP iNj ?? ??? ??? PostH.
  apply:himpl_trans; first eauto.
  rewrite /ntriple /nwp ?fset_of_cons /=.
  apply: himpl_trans; first last.
  { apply/wp_conseq=> ?; apply PostH. }
  rewrite ?Union_label union_empty_r.
  eapply wp_for with 
    (H:=(fun q hv => 
      Inv q \* 
      (\*_(d <- Union (interval Z q) fsi1) R' d) \*
      (\*_(d <- Union (interval q N) fsi1) R d) \* 
      p ~⟨(i, 0%Z), s⟩~> Σ_(l <- interval Z q) op hv l))
    (hv0:=fun=> 0)=> //; try eassumption.
  { clear -IH Dj iNj opP.
    move=>l hv ?; move: (IH l).
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
    rewrite union_empty_r intervalUr; try math.
    rewrite Union_upd // hbig_fset_union; first last.
    2-4: auto.
    2-3: hnf; auto.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    rewrite (@intervalU l N); last math.
    rewrite Union_upd // hbig_fset_union; first last.
    2-4: auto.
    2-3: hnf; auto.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    move=> Hwp.
    erewrite wp_ht_eq with (ht2:=(htrm_of
      ((Lab (pair i 0) (FH (single s tt) (fun=> subst vr l C))) ::
        (Lab (pair j 0) (FH (fsi1 l) (fun ld => C1 ld))) ::
        nil))).
    2:{
      intros (ll, d) H. unfold uni, htrm_of. simpl. 
      rewrite indom_union_eq ! indom_label_eq in H |- *.
      rewrite indom_single_eq in H |- *. 
      repeat case_if; try eqsolve.
      destruct C3 as (<- & HH). false C2. split; auto.
      rewrite indom_Union. exists l. rewrite indom_interval.
      split; try math; auto.
    }
    assert (Z <= l < N) as Htmp by math. 
    specialize (Hwp (Sum (interval Z l) (fun i => op hv i)) Htmp). clear Htmp.
    apply wp_equiv in Hwp. apply wp_equiv.
    eapply htriple_conseq_frame.
    1: apply Hwp.
    1: xsimpl. 1: xsimpl.
    hnf. intros v.
    xsimpl. xsimpl.
    rewrite <- intervalUr; try math. rewrite SumxSx; try math.
    hnf. intros h Hh. apply hsingle_inv in Hh. subst h.
    rewrite -> SumEq with (G:=fun i => op hv i).
    2:{ intros x. rewrite indom_interval. 
      unfold uni. intros HH. apply opP.
      intros. rewrite indom_label_eq. case_if; auto.
      destruct C0 as (_ & H0).
      false disjoint_inv_not_indom_both. 2: apply H. 2: apply H0.
      apply Dj. math.
    }
    rewrite -> opP with (hv':=v). 1: apply hsingle_intro.
    intros. unfold uni. rewrite indom_label_eq. case_if; eqsolve. }
  { move=> r hv hv' hvE.
    suff->:
      Σ_(l <- interval Z r) op hv l = 
      Σ_(l <- interval Z r) op hv' l by xsimpl.
    apply/SumEq=> *; apply/opP=> *; apply/hvE.
    rewrite indom_Union; eexists; rewrite indom_label_eq; autos*. }
  { rewrite [_ Z Z]intervalgt; last math.
    rewrite Union0 hbig_fset_empty Sum0. xsimpl. }
  { move=> ?.
    rewrite [_ N N]intervalgt; last math.
    rewrite Union0 hbig_fset_empty. xsimpl. }
  { simpl.
    intros. apply disjoint_of_not_indom_both. 
    intros. destruct x as (?, x). 
    rewrite indom_label_eq in H0. rewrite indom_label_eq in H1.
    destruct H0 as (_ & H0), H1 as (_ & H1). 
    revert H0 H1. by apply disjoint_inv_not_indom_both, Dj.
  }
  { rewrite disjoint_Union=> ??. 
    apply disjoint_of_not_indom_both. 
    intros. destruct x as (?, x).
    simpl in H. rewrite indom_single_eq in H.  
    injection H as <-.
    rewrite -> indom_Union in H0.
    destruct H0 as (? & ? & H0).
    rewrite indom_label_eq in H0. eqsolve.
  }
  by case=> l d; rewrite indom_label_eq /= /htrm_of; case: classicT.
Qed.

(* the original wp_for is good. *)
Lemma xfor_specialized_lemma (Inv : int -> hhprop) (R R' : IntDom.type -> hhprop) 
  s fsi1 vr
  Z N (C1 : IntDom.type -> trm) (i j : int) (C : trm)
  Pre Post
  (p : int -> loc) : 
  (forall (l : int),
    Z <= l < N ->
    {{ Inv l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R d) \*
       (\*_(d <- (fsi1 l)) p d ~⟨(i, 0%Z), s⟩~> val_uninit) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' d) \*
        (\*_(d <- (fsi1 l)) p d ~⟨(i, 0%Z), s⟩~> hv (Lab (j, 0%Z) d)) }}) ->
  (forall i0 j0 : int, i0 <> j0 -> disjoint (fsi1 i0) (fsi1 j0)) ->
  (i <> j) ->
  (Z <= N)%Z ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi1) R d) \*
    (\*_(d <- Union (interval Z N) fsi1) p d ~⟨(i, 0%Z), s⟩~> val_uninit)) ->
  (forall hv,
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi1) R' d) \*
    (\*_(d <- Union (interval Z N) fsi1) p d ~⟨(i, 0%Z), s⟩~> hv (Lab (j, 0%Z) d)) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For Z N (trm_fun vr C)};
      {j| ld in Union (interval Z N) fsi1 => C1 ld}
    }]
  {{ hv, Post hv }}.
Proof.
  move=> IH Dj iNj ?? ??? ??? PostH.
  apply:himpl_trans; first eauto.
  rewrite /ntriple /nwp ?fset_of_cons /=.
  apply: himpl_trans; first last.
  { apply/wp_conseq=> ?; apply PostH. }
  rewrite ?Union_label union_empty_r.
  eapply wp_for with 
    (H:=(fun q hv => 
      Inv q \* 
      (\*_(d <- Union (interval Z q) fsi1) R' d) \*
      (\*_(d <- Union (interval q N) fsi1) R d) \* 
      (\*_(d <- Union (interval Z q) fsi1) p d ~⟨(i, 0%Z), s⟩~> hv (Lab (j, 0%Z) d)) \*
      (\*_(d <- Union (interval q N) fsi1) p d ~⟨(i, 0%Z), s⟩~> val_uninit)))
    (hv0:=fun=> 0) => //; try eassumption.
  { clear -IH Dj iNj.
    move=>l hv ?. 
    move: (IH l).
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
    rewrite union_empty_r intervalUr; try math.
    rewrite Union_upd // hbig_fset_union; first last.
    2-4: auto.
    2-3: hnf; auto.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    rewrite (@intervalU l N); last math.
    rewrite Union_upd // hbig_fset_union; first last.
    2-4: auto.
    2-3: hnf; auto.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    move=> Hwp.
    rewrite -> hbig_fset_union.
    2-3: hnf; auto.
    2: auto.
    2: { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    erewrite wp_ht_eq with (ht2:=(htrm_of
      ((Lab (pair i 0) (FH (single s tt) (fun=> subst vr l C))) ::
        (Lab (pair j 0) (FH (fsi1 l) (fun ld => C1 ld))) ::
        nil))).
    2:{
      intros (ll, d) H. unfold uni, htrm_of. simpl. 
      rewrite indom_union_eq ! indom_label_eq in H |- *.
      rewrite indom_single_eq in H |- *. 
      repeat case_if; try eqsolve.
      destruct C3 as (<- & HH). false C2. split; auto.
      rewrite indom_Union. exists l. rewrite indom_interval.
      split; try math; auto.
    }
    assert (Z <= l < N) as Htmp by math. specialize (Hwp Htmp). clear Htmp.
    apply wp_equiv in Hwp. apply wp_equiv.
    eapply htriple_conseq_frame.
    1: apply Hwp.
    1: xsimpl. 1: xsimpl.
    hnf. intros v.
    xsimpl. xsimpl.
    rewrite -> hbig_fset_union.
    2-3: hnf; auto.
    2: auto.
    2: { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    unfold uni.
    apply himpl_frame_lr.
    { apply hbig_fset_himpl.
      intros. case_if; auto.
      rewrite indom_label_eq in C0. eqsolve.
    }
    { apply hbig_fset_himpl.
      intros. case_if; auto.
      rewrite indom_label_eq in C0. destruct C0 as (_ & H1).
      rewrite indom_Union in H. 
      destruct H as (f & H & H2). rewrite -> indom_interval in H.
      false. revert H1 H2. apply disjoint_inv_not_indom_both, Dj.
      math.
    }
  }
  { intros. f_equal. f_equal. f_equal. f_equal. apply hbig_fset_eq.
    intros. rewrite -> H; auto.
    rewrite indom_Union in H0. rewrite indom_Union.
    destruct H0 as (f & H0 & H2). 
    exists f. rewrite indom_label_eq. intuition.
  }
  { rewrite [_ Z Z]intervalgt; last math.
    rewrite Union0 ! hbig_fset_empty. xsimpl. }
  { move=> ?.
    rewrite [_ N N]intervalgt; last math.
    rewrite Union0 ! hbig_fset_empty. xsimpl. }
  { simpl.
    intros. apply disjoint_of_not_indom_both. 
    intros. destruct x as (?, x). 
    rewrite indom_label_eq in H0. rewrite indom_label_eq in H1.
    destruct H0 as (_ & H0), H1 as (_ & H1). 
    revert H0 H1. by apply disjoint_inv_not_indom_both, Dj.
  }
  { rewrite disjoint_Union=> ??. 
    apply disjoint_of_not_indom_both. 
    intros. destruct x as (?, x).
    simpl in H. rewrite indom_single_eq in H.  
    injection H as <-.
    rewrite -> indom_Union in H0.
    destruct H0 as (? & ? & H0).
    rewrite indom_label_eq in H0. eqsolve.
  }
  by case=> l d; rewrite indom_label_eq /= /htrm_of; case: classicT.
Qed.

Section Programs.

Definition rlsum_loopbody (real_x_ind real_x_val real_s real_i : trm) :=
  (* need to make it a term; otherwise subst cannot penetrate *)
  <{  let "tmp1" = ! real_s in
      let "tmp2" = val_array_get real_x_val real_i in
      let "tmp3" = real_i + 1 in
      let "tmp4" = val_array_get real_x_ind "tmp3" in
      let "tmp5" = val_array_get real_x_ind real_i in
      let "tmp6" = "tmp4" - "tmp5" in
      let "tmp7" = "tmp2" * "tmp6" in
      let "tmp8" = "tmp1" + "tmp7" in
      real_s := "tmp8" }>.

Definition rlsum_func (M : int) :=
  let loopbody := rlsum_loopbody "x_ind" "x_val" "s" "i" in
  let loop := For 0 M (trm_fun "i" loopbody) in
  (* the arguments should be the location of arrays? *)
  <{ fun "x_ind" "x_val" => 
      let "s" = ref 0 in 
      loop ; 
      let "res" = ! "s" in
      free "s"; 
      "res"
  }>.

Definition rli_whilecond (i : int) (real_x_ind real_j : trm) :=
  (* intermediate lang *)
  (<{ let "tmp1" = ! real_j in
      let "tmp2" = "tmp1" + 1 in
      let "tmp3" = val_array_get real_x_ind "tmp2" in
      "tmp3" <= i }>).

Definition incr (real_j : trm) :=
  (<{ let "tmp1" = ! real_j in
      let "tmp2" = "tmp1" + 1 in
      real_j := "tmp2" }>).

Definition rli_whilebody := Eval unfold incr in incr.

Definition rli_func (i : int) :=
  let loop := While (rli_whilecond i "x_ind" "j")
    (rli_whilebody "j") in
  <{ fun "x_ind" "x_val" => 
      let "j" = ref 0 in 
      loop ; 
      let "tmp" = ! "j" in 
      free "j";
      (val_array_get "x_val" "tmp")
  }>.

Definition rl_loopbody (real_x real_x_ind real_x_val real_i real_k : trm) :=
  let inc := rli_whilebody real_i in
  <{  let "tmp1" = ! real_i in
      let "tmp2" = val_array_get real_x_val "tmp1" in
      val_array_set real_x real_k "tmp2";
      let "lhs" = real_k + 1 in
      let "tmp3" = "tmp1" + 1 in
      let "rhs" = val_array_get real_x_ind "tmp3" in
      let "cmp" = "lhs" >= "rhs" in
      if "cmp" then inc end }>.

Definition rl_func (N : int) :=
  let loopbody := rl_loopbody "x" "x_ind" "x_val" "i" "k" in
  let loop := For 0 N (trm_fun "k" loopbody) in
  let al := abs N in
  <{ fun "x_ind" "x_val" =>
      let "x" = val_alloc al in
      let "i" = ref 0 in 
      loop ; 
      free "i"; 
      "x"
  }>.

End Programs.

Section Demo.

(* should not mix notations on nat and Z ... *)

Variables (N M : int) (Lval : list int) (Lind : list int).
Hypothesis H_length_Lval : length Lval = abs M.
Hypothesis H_length_Lind : length Lind = abs (M + 1).
Hypothesis H_Lind_first : nth 0%nat Lind = 0.
Hypothesis H_Lind_last : nth (abs M) Lind = N.
Hypothesis H_Lind_inc : forall (i j : nat), 
  (0 <= (nat_to_Z i) <= abs M)%Z -> 
  (0 <= (nat_to_Z j) <= abs M)%Z -> 
  (i < j)%nat -> 
  (nth i Lind < nth j Lind)%Z.
Hypothesis H_Lval_notnil : (0 < M)%Z.

Fact H_Lind_inc' : forall (i j : int), 
  (0 <= i <= M)%Z -> 
  (0 <= j <= M)%Z -> 
  (i <= j)%Z -> 
  (nth (abs i) Lind <= nth (abs j) Lind)%Z.
Proof using M Lind H_Lind_inc.
  clear N Lval H_length_Lval H_length_Lind H_Lval_notnil H_Lind_last H_Lind_first.

  intros. destruct (Z.eqb i j) eqn:E.
  { rewrite -> Z.eqb_eq in E. subst i. reflexivity. }
  { rewrite -> Z.eqb_neq in E. assert (i < j)%Z by math.
    match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end. 
    apply H_Lind_inc; math.
  }
Qed. 

Fact zero_lt_N : (0 < N)%Z.
Proof using N M Lind H_Lind_inc H_Lind_first H_Lind_last H_Lval_notnil.
  clear Lval H_length_Lval H_length_Lind.

  (* extract? *)
  rewrite <- H_Lind_first, <- H_Lind_last. 
  change 0%nat with (abs 0).
  apply H_Lind_inc; math.
Qed.

Fact zero_le_N : (0 <= N)%Z.
Proof using N M Lind H_Lind_inc H_Lind_first H_Lind_last H_Lval_notnil.
  clear Lval H_length_Lval H_length_Lind.

  pose proof zero_lt_N. math.
Qed.

Definition arr_x_ind (p : loc) (d : D) :=
  harray (LibList.map val_int Lind) p d.

Definition arr_x_val (p : loc) (d : D) :=
  harray (LibList.map val_int Lval) p d.

Section Segmentation.

Definition ind_seg (i : int) := 
  interval (nth (abs i) Lind) (nth (abs (i + 1)) Lind).

Lemma interval_segmentation_pre i :
  0 <= i <= M -> 
  Union (interval 0 i) ind_seg = interval 0 (nth (abs i) Lind).
Proof using N M Lind H_length_Lind H_Lind_first H_Lind_inc.
  clear Lval H_length_Lval H_Lind_last H_Lval_notnil.

  remember (to_nat i) as n.
  revert i Heqn.
  induction n as [ | n IH ]; intros.
  { assert (i = 0) as -> by math. 
    replace (abs 0) with O by math. 
    rewrite -> H_Lind_first. simpl. rewrite -> intervalgt; try math.
    by rewrite -> Union0.
  }
  { assert (i = (nat_to_Z n) + 1) as -> by math.
    rewrite -> intervalUr; try math.
    rewrite -> Union_upd_fset, -> IH; try math.
    unfold ind_seg. 
    replace ((abs n)) with n by math.
    replace (abs (n + 1)) with (S n) by math.
    rewrite <- interval_union with (x:=0) (y:=(nth n Lind))
      (z:=(nth (S n) Lind)); try math.
    2:{
      rewrite <- H_Lind_first. 
      destruct n; try math. 
      match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end. 
      apply H_Lind_inc; math. 
    }
    2:{ match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end. 
      apply H_Lind_inc; math. 
    }
    rewrite -> union_comm_of_disjoint. 1: reflexivity.
    apply disjoint_of_not_indom_both.
    intros. rewrite -> indom_interval in *. math.
  }
Qed.

Lemma ind_seg_disjoint (i j : int) (Hi : indom (interval 0 M) i)
  (Hj : indom (interval 0 M) j) (Hn : i <> j) : disjoint (ind_seg i) (ind_seg j).
Proof.
  unfold ind_seg. 
  rewrite -> indom_interval in Hi, Hj.
  destruct Hi as (Hi1 & Hi2), Hj as (Hj1 & Hj2).
  apply disjoint_of_not_indom_both.
  intros x Hi Hj. rewrite -> indom_interval in Hi, Hj.
  destruct (Z.leb (i + 1) j) eqn:E.
  { rewrite -> Z.leb_le in E.
    apply H_Lind_inc' in E; try math.
  }
  { destruct (Z.leb (j + 1) i) eqn:E'.
    { rewrite -> Z.leb_le in E'.
      apply H_Lind_inc' in E'; try math.
    }
    rewrite -> Z.leb_gt in E, E'.
    math.
  }
Qed.

Lemma interval_segmentation :
  Union (interval 0 M) ind_seg = interval 0 N.
Proof using N M Lind H_length_Lind H_Lind_first H_Lind_inc H_Lind_last H_Lval_notnil.
  clear Lval H_length_Lval.

  rewrite -> interval_segmentation_pre with (i:=M). 2: math.
  rewrite <- H_Lind_last.
  f_equal.
Qed.

Lemma segmentation_sum hv (i : int) (Hi : (0 <= i <= M)%Z) : 
  val_int (fset_fold 0
    (fun idx : int =>
    Z.add^~ (fset_fold 0
                (fun d : labeled int =>
                Z.add^~ match hv d with
                        | val_int n => n
                        | _ => 0
                        end) ⟨(2, 0), ind_seg idx⟩)) 
    (interval 0 i)) =
  fset_fold (val_int 0) (fun (d : labeled int) (acc : val) => val_int_add acc (hv d))
    ⟨(2, 0), interval 0 (nth (abs i) Lind)⟩.
Proof.
  remember (abs i) as n eqn:E.
  revert i Hi E. 
  induction n; intros.
  { change (abs 0)%Z with 0%nat. 
    assert (i=0) as -> by math.
    rewrite -> H_Lind_first.
    rewrite -> intervalgt; try math.
    rewrite label_empty. 
    rewrite -> ! (fst (@fset_foldE _ _ _ _)); auto.
  }
  { replace i with ((i - 1) + 1)%Z by math.
    rewrite -> E.
    rewrite <- interval_union with (x:=0) (y:=(nth (abs (i-1)) Lind))
      (z:=(nth (abs i) Lind)); try math.
    2:{ rewrite <- H_Lind_first. 
      replace 0%nat with (abs 0) by math.
      apply H_Lind_inc'; math. 
    }
    2: apply H_Lind_inc'; math. 
    rewrite -> intervalUr. 2: math.
    rewrite -> (snd (@fset_foldE _ _ _ _)); try math.
    2:{ rewrite -> indom_interval. intros ?. math. }
    rewrite -> val_int_add_distr, -> IHn; try math.
    replace n with (abs (i - 1)) by math.
    rewrite -> val_int_add_fold_transform.
    rewrite label_union.
    symmetry.
    unfold ind_seg. replace (i - 1 + 1) with i by math.
    rewrite -> fset_fold_val_int_add_union; try reflexivity.

    apply disjoint_of_not_indom_both.
    intros (?, ?) H H'. 
    rewrite indom_label_eq in H.
    rewrite indom_label_eq in H'.
    destruct H as (<- & H), H' as (_ & H').
    rewrite -> indom_interval in H, H'. math.
  }
Qed.

End Segmentation.

Section MainProof.

Lemma rli_whilecond_spec : forall (j k : int) (pj0 px_ind : loc) (d : D)
  (Hj : (0 <= j < M)%Z),
  (pj0 ~(d)~> j \* arr_x_ind px_ind d) ==>
  wp (single d tt) (fun=> rli_whilecond k px_ind pj0) 
    (fun hv => \[hv d = (Z.leb (nth (abs (j+1)) Lind) k)] \* pj0 ~(d)~> j \* arr_x_ind px_ind d).
Proof.
  intros.
  xwp. xlet.
  (* hard to only wp *)
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> j).
  1:{
    replace (pj0 ~(d)~> j) with (\*_(d0 <- single d tt) (pj0 ~(d0)~> j)).
    2: apply hbig_fset_label_single'.
    apply htriple_get.
  }
  1: apply himpl_refl.
  xsimpl.
  intros ? ->.
  xwp. xlet. xapp.
  xwp. xlet.
  (* use array opr triple *)
  apply wp_equiv.

  (* again? *)
  eapply htriple_conseq_frame with (H1:=arr_x_ind px_ind d).
  1:{ 
    replace (arr_x_ind px_ind d) with 
      (\*_(d0 <- single d tt) (arr_x_ind px_ind d0)).
    2: apply hbig_fset_label_single'.
    apply htriple_array_get.
    { intros. rewrite -> length_map, -> H_length_Lind. math. }
    { intros. reflexivity. } 
  }
  1: xsimpl.
  xsimpl.
  introv Er. specialize (Er d (indom_single _ _)).

  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=\[]).
  1:{
    apply wp_equiv. 
    rewrite -> wp_ht_eq with (ht2:=fun=> trm_app (trm_app val_le (r d)) k).
    2:{
      introv H. rewrite -> indom_single_eq in H. by subst.
    }
    (* bad *)
    apply wp_equiv, htriple_binop.
    introv H. 
    instantiate (1:=fun=> (Z.leb (nth (abs (j+1)) Lind) k)). simpl.
    rewrite -> Er.
    pose proof (evalbinop_le (nth (abs (j+1)) Lind) k) as HH.
    rewrite -> nth_map. 2: math.
    rewrite -> isTrue_eq_if in HH.
    case_if. 
    { assert (nth (abs (j + 1)) Lind <=? k = true)%Z as ->; auto.
      apply Z.leb_le. math.
    }
    { assert (nth (abs (j + 1)) Lind <=? k = false)%Z as ->; auto.
      apply Z.leb_gt. math.
    }
  }
  1: rewrite -> hstar_hempty_l; apply himpl_refl.
  xsimpl. 1: intros ? ->; reflexivity.
  intros ? ->.
  rewrite -> ! hbig_fset_label_single'.
  xsimpl.
Qed.

Lemma rli_whilebody_spec : forall (pj0 : loc) (d : D) (j : int),
  (pj0 ~(d)~> j) ==>
  wp (single d tt) (fun=> rli_whilebody pj0) 
    (fun=> pj0 ~(d)~> (j+1)).
Proof using.
  intros.
  unfold rli_whilebody.
  xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H2:=\[]).
  2: xsimpl.
  1:{ 
    rewrite <- hbig_fset_label_single' with (Q:=fun d0 => pj0 ~(d0)~> j).
    apply htriple_get.
  }
  xsimpl.
  intros ? ->.
  xwp. xlet. xapp. xapp. by rewrite -> hbig_fset_label_single'.
Qed.

(* using While on a single program *)
Lemma rli_func_spec : forall (d : D) (px_ind px_val : loc) (k : int)
  (Hk : (0 <= k < N)%Z) (a : int) (Ha : (0 <= a < M)%Z) 
  (Hka : (nth (abs a) Lind <= k < nth (abs (a + 1)) Lind)%Z), 
  htriple (single d tt) 
    (fun=> rli_func k px_ind px_val)
    (arr_x_ind px_ind d \* arr_x_val px_val d)
    (fun hv => \[hv d = val_int (nth (abs a) Lval)] \* arr_x_ind px_ind d \* arr_x_val px_val d).
Proof.
  intros. 
  unfold rli_func.
  (* do app2 for rlsum *)
  eapply htriple_eval_like.
  1: apply eval_like_app_fun2; eqsolve.
  (* subst pushdown *)
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  (* assign location *)

  eapply htriple_let.
  1:{ 
    rewrite <- hstar_hempty_l at 1.
    eapply htriple_frame. apply htriple_ref.
  }
  intros. simpl. 
  (* simplify hexists *)
  apply wp_equiv.
  xsimpl. intros pj ->. xsimpl.
  (* use only one point location of pj; then forget pj *)
  remember (pj d) as pj0.
  erewrite -> wp_ht_eq with (ht2:=
    fun=> trm_seq (While (rli_whilecond k px_ind pj0) (rli_whilebody pj0)) 
      (trm_let "tmp" (val_get pj0) (trm_seq (val_free pj0)
          (val_array_get px_val "tmp")))).
  2:{ 
    intros. unfolds While, While_aux, rli_whilecond, rli_whilebody. 
    rewrite -> indom_single_eq in H. by subst.
  }
  apply wp_equiv.
  eapply htriple_conseq.
  3: apply qimpl_refl.
  2:{
    apply himpl_frame_l with (H1':=pj0 ~(d)~> 0). subst pj0.
    rewrite -> update_empty, -> hbig_fset_update, -> hbig_fset_empty; auto.
    xsimpl.
  }
  clear pj Heqpj0.
  (* use single wp_while here *)
  apply wp_equiv.
  xwp. xseq.
  apply wp_equiv.

  (* first have to check if a = 0 or not; slightly troublesome here *)
  remember (abs a) as n eqn:E.
  destruct n as [ | n ].
  1:{
    replace a with 0 in * by math.
    replace (0+1) with 1 in * by math.
    replace (abs 1) with 1%nat in Hka by math.

    unfold While, While_aux, rli_whilecond.
    apply wp_equiv. rewrite -> wp_fix_app2. 
    apply wp_equiv, htriple_app_fix_direct.
    simpl.
    apply wp_equiv.    
    xwp. xlet.

    (* use the spec above *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> 0 \* arr_x_ind px_ind d).
    2: xsimpl.
    1:{ apply wp_equiv, rli_whilecond_spec. math. }
    xsimpl.
    intros r Er.
    change (abs (0 + 1)) with 1%nat in Er.

    (* ready for the rest *)
    match goal with |- himpl _ (wp _ ?ht _) => pose (ff:=ht) end.
    erewrite -> wp_ht_eq with (ht2:=fun=> ff d).
    2:{ 
      intros. rewrite -> indom_single_eq in H. by subst.
    }
    subst ff. simpl.
    destruct Hka as (_ & Hka).
    rewrite <- Z.leb_gt in Hka.
    rewrite -> Hka in Er.
    xwp. rewrite -> Er. xif. 1: intros; by false.
    intros _. 
    xwp. xval. 
    xwp. xlet.
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> 0).
    1:{
      replace (pj0 ~(d)~> 0) with (\*_(d0 <- single d tt) (pj0 ~(d0)~> 0)).
      2: apply hbig_fset_label_single'.
      apply htriple_get.
    }
    1: apply himpl_refl.
    xsimpl.
    intros ? ->.
    xwp. xseq. xwp. xapp.

    (* restore the thing array get after seq *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=arr_x_val px_val d).
    1:{ 
      replace (arr_x_val px_val d) with 
        (\*_(d0 <- single d tt) (arr_x_val px_val d0)).
      2: apply hbig_fset_label_single'.
      apply htriple_array_get.
      { intros. rewrite -> length_map, -> H_length_Lval. math. }
      { intros. reflexivity. } 
    }
    1: xsimpl.
    xsimpl.
    { 
      introv Er0. specialize (Er0 d (indom_single _ _)).
      rewrite -> Er0, -> nth_map; math.
    }
    {
      introv Er0. specialize (Er0 d (indom_single _ _)).
      rewrite -> ! hbig_fset_label_single'.
      xsimpl.
    }
  }

  assert (0 < a < M)%Z as (Ha1 & Ha2) by math.
  rewrite -> E in Hka.
  (* use single wp_while here *)
  rewrite <- union_empty_r with (h:=single d tt).
  apply wp_equiv.
  eapply wp_while with (fsi:=fun=> empty) (s:=d) (Z:=0) (N:=a) (b0:=true) (hv0:=fun=> val_unit)
    (Inv:=fun b j _ => \[(0 <= j < M)%Z /\
      (nth (abs j) Lind <= k)%Z /\ b = Z.leb (nth (abs (j+1)) Lind) k] 
      \* pj0 ~(d)~> j \* arr_x_ind px_ind d \* arr_x_val px_val d)
    (HC:=fun c b j _ => \[(0 <= j < M)%Z /\ c = b /\ 
      (nth (abs j) Lind <= k)%Z /\ b = Z.leb (nth (abs (j+1)) Lind) k] 
      \* pj0 ~(d)~> j \* arr_x_ind px_ind d \* arr_x_val px_val d).
  17: reflexivity.
  9-15: auto; try math.
  8: by rewrite -> UnionN0.
  7: math.
  7: intros; auto.
  { intros b j _. xsimpl. intros (H1 & H2 & ->).
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> j \* arr_x_ind px_ind d).
    1:{ apply wp_equiv, rli_whilecond_spec. math. }
    1: xsimpl.
    xsimpl.
    { intros. rewrite H. reflexivity. }
    { intros. auto. }
  }
  { intros b j _. xsimpl.
    { intros (Hj & <- & Hleb & EE).
      symmetry in EE.
      split; auto.
      (* here is the unique proof *)
      rewrite -> Z.leb_gt in EE.
      destruct Hka as (Hka1 & Hka2).
      destruct (Z.leb (j+1) a) eqn:Eu.
      { rewrite -> Z.leb_le in Eu.
        enough (nth (abs (j + 1)) Lind <= nth (abs a) Lind)%Z by math.
        apply H_Lind_inc'; math.
      }
      { destruct (Z.leb (a+1) j) eqn:Eu'.
        { rewrite -> Z.leb_le in Eu'.
          enough (nth (abs (a + 1)) Lind <= nth (abs j) Lind)%Z by math.
          apply H_Lind_inc'; math.
        }
        { rewrite -> Z.leb_gt in Eu, Eu'. math. }
      }
    }
    { intros (Hj & <- & Hleb & EE).
      split; auto.
    }
  }
  { intros b j hv (Hj1 & Hj2) IH.
    xsimpl. intros (_ & <- & H1 & H2).
    symmetry in H2. rewrite -> Z.leb_le in H2.
    rewrite -> UnionN0, -> union_empty_r.
    rewrite -> wp_ht_eq with (ht2:=fun=> trm_seq (rli_whilebody pj0) 
       (While (rli_whilecond k px_ind pj0) (rli_whilebody pj0))).
    2:{ 
      introv HH. unfold upd. 
      rewrite -> indom_single_eq in HH. subst. case_if; eqsolve.
    }
    xwp. xseq.

    (* body: a simple incr *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> j).
    2: xsimpl.
    1: apply wp_equiv; apply rli_whilebody_spec.
    xsimpl.

    destruct (Z.leb (a-1) j) eqn:Ef.
    { (* check if it is the end *)
      rewrite -> Z.leb_le in Ef.
      assert (j = a - 1) as -> by math.
      replace (a - 1 + 1) with a in * by math.
      
      (* script reuse *)
      unfold While, While_aux, rli_whilecond.
      rewrite -> wp_fix_app2. 
      apply wp_equiv, htriple_app_fix_direct.
      simpl.
      apply wp_equiv.    
      xwp. xlet.

      (* use the spec above *)
      apply wp_equiv.
      eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> a \* arr_x_ind px_ind d).
      2: xsimpl.
      1:{ apply wp_equiv, rli_whilecond_spec. math. }
      xsimpl.
      intros r Er.

      (* ready for the rest *)
      match goal with |- himpl _ (wp _ ?ht _) => pose (ff:=ht) end.
      erewrite -> wp_ht_eq with (ht2:=fun=> ff d).
      2:{ 
        intros. rewrite -> indom_single_eq in H. by subst.
      }
      subst ff. simpl.
      destruct Hka as (_ & Hka).
      rewrite <- Z.leb_gt in Hka.
      rewrite -> Hka in Er.
      xwp. rewrite -> Er. xif. 1: intros; by false.
      intros _. 
      xwp. xval.

      xsimpl. split; auto. eqsolve.
    }
    { (* use IH *)
      rewrite -> Z.leb_gt in Ef. clear Hj2.
      assert (j + 1 < a)%Z as Hj2 by math.
      assert (j < j + 1)%Z as Hj3 by math.
      specialize (IH (j+1) true (fun=> val_unit) (conj Hj3 Hj2)).
      rewrite -> UnionN0, -> union_empty_r in IH.
      rewrite -> wp_ht_eq with (ht2:=fun=> 
        (While (rli_whilecond k px_ind pj0) (rli_whilebody pj0))) in IH.
      2:{ 
        introv HH. unfold upd. 
        rewrite -> indom_single_eq in HH. subst. case_if; eqsolve.
      }
      apply wp_equiv.
      destruct Hka as (Hka1 & Hka2).
      eapply htriple_conseq.
      1: apply wp_equiv, IH.
      { xsimpl. split; try math. split; try assumption. 
        symmetry. apply Z.leb_le.
        transitivity (nth (abs a) Lind); try assumption. 
        destruct (Z.leb a (j+1+1)) eqn:EE.
        { rewrite -> Z.leb_le in EE.
          assert (j+1+1 = a) as -> by math.
          reflexivity.
        }
        { rewrite -> Z.leb_gt in EE.
          match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end.
          apply H_Lind_inc; math.
        }
      }
      auto.
    }
  }
  { intros. auto. }
  { xsimpl. split; try math. destruct Hka as (Hka1 & Hka2). split.
    { transitivity (nth (abs a) Lind); try assumption.
      match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end.
      apply H_Lind_inc; math.
    }
    { symmetry. apply Z.leb_le. change (0+1) with 1.
      transitivity (nth (abs a) Lind); try assumption.
      destruct n. 1: replace a with 1 by math; reflexivity.
      match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end.
      apply H_Lind_inc; math.
    }
  }
  { xsimpl. intros _ (_ & H1 & H2).
    symmetry in H2. rewrite -> Z.leb_gt in H2.
    rewrite -> E, -> union_empty_r.

    (* again the rest part? *)
    xwp. xlet.
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> a).
    1:{
      replace (pj0 ~(d)~> a) with (\*_(d0 <- single d tt) (pj0 ~(d0)~> a)).
      2: apply hbig_fset_label_single'.
      apply htriple_get.
    }
    1: apply himpl_refl.
    xsimpl.
    intros ? ->.
    xwp. xseq. xwp. xapp. 

    (* restore the thing array get after seq *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=arr_x_val px_val d).
    1:{ 
      replace (arr_x_val px_val d) with 
        (\*_(d0 <- single d tt) (arr_x_val px_val d0)).
      2: apply hbig_fset_label_single'.
      apply htriple_array_get.
      { intros. rewrite -> length_map, -> H_length_Lval. math. }
      { intros. reflexivity. } 
    }
    1: xsimpl.
    xsimpl.
    { 
      introv Er0. specialize (Er0 d (indom_single _ _)).
      rewrite -> Er0, -> nth_map; math.
    }
    {
      introv Er0. specialize (Er0 d (indom_single _ _)).
      rewrite -> ! hbig_fset_label_single'.
      xsimpl.
    }
  }
Qed.

Lemma rlsum_loopbody_spec d (x : int) (px_ind px_val : loc) (ps0 : loc) (l : int) (Hl : (0 <= l < M)%Z) :
  htriple (single d tt) (fun=> rlsum_loopbody px_ind px_val ps0 l)
    (ps0 ~(d)~> x \* arr_x_val px_val d \* arr_x_ind px_ind d)
    (fun hv => ps0 ~(d)~> (x + ((nth (abs l) Lval) * ((nth (abs (l+1)) Lind) - (nth (abs l) Lind)))%Z) 
      \* arr_x_val px_val d \* arr_x_ind px_ind d).
Proof.
  unfold rlsum_loopbody.
  apply wp_equiv.
  xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame.
  2: apply himpl_refl.
  1:{ 
    rewrite <- hbig_fset_label_single' with (Q:=fun d0 => ps0 ~(d0)~> x).
    apply htriple_get.
  }
  xsimpl. intros ? ->.
  xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=arr_x_val px_val d).
  2: xsimpl.
  1:{
    rewrite <- hbig_fset_label_single' with (Q:=fun d0 => arr_x_val px_val d0).
    apply htriple_array_get.
    { intros. rewrite -> length_map, -> H_length_Lval. math. }
    { intros. reflexivity. }
  }
  xsimpl. intros r Hr.
  specialize (Hr _ (indom_single d _)).
  xwp. xlet. xapp.
  xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=arr_x_ind px_ind d).
  2: xsimpl.
  1:{
    rewrite <- hbig_fset_label_single' with (Q:=fun d0 => arr_x_ind px_ind d0).
    apply htriple_array_get.
    { intros. rewrite -> length_map, -> H_length_Lind. math. }
    { intros. reflexivity. }
  }
  xsimpl. intros r0 Hr0.
  specialize (Hr0 _ (indom_single d _)).
  xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame.
  2: apply himpl_refl.
  1:{
    apply htriple_array_get.
    { intros. rewrite -> length_map, -> H_length_Lind. math. }
    { intros. reflexivity. }
  }
  xsimpl. intros r1 Hr1.
  specialize (Hr1 _ (indom_single d _)).
  rewrite -> wp_ht_eq with (ht2:=fun=> 
  let aa := r0 d in let bb := r1 d in let cc := r d in
    <{
    let "tmp6" = aa - bb in
    let "tmp7" = cc * "tmp6" in
    let "tmp8" = x + "tmp7" in
    ps0 := "tmp8" }>).
  2:{ intros. rewrite -> indom_single_eq in H. subst. by simpl. }
  simpl. rewrite -> Hr, Hr0, Hr1.
  rewrite -> ! nth_map; try math.
  xwp. xlet. xapp. xwp. xlet. xapp. xwp. xlet. xapp.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=(\*_(d0 <- single d tt) ps0 ~(d0)~> x)).
  2: xsimpl.
  1: apply htriple_set.
  xsimpl.
  rewrite -> ! hbig_fset_label_single'. xsimpl.
Qed.

(* two different forms of summation spec *)

Lemma rlsum_rli_align_step : forall (px_ind px_val : loc) (ps0 : loc),
  ntriple 
    (ps0 ~⟨(1%Z, 0%Z), 0⟩~> 0 \*
      arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
      arr_x_val px_val (⟨(1, 0), 0⟩)%arr \*
      (\*_(d <- interval 0 N)
          arr_x_ind px_ind (⟨(2, 0), d⟩)%arr \*
          arr_x_val px_val (⟨(2, 0), d⟩)%arr))
    ((Lab (pair 1 0) 
        (FH (single 0 tt) (fun=> 
          For 0 M (trm_fun "i" (rlsum_loopbody (val_loc px_ind) (val_loc px_val) (val_loc ps0) "i"))
          ))) :: 
      (Lab (pair 2 0) 
        (FH (Union (interval 0 M) ind_seg) 
          (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => (fun hveta => ps0 ~⟨(1%Z, 0%Z), 0⟩~> 
      (fset_fold (val_int 0) 
        (* (fun d acc => int_add_val_int acc (hveta d)) *)
        (fun d acc => val_int_add acc (hveta d))
        (label (Lab (pair 2 0) (interval 0 N)))) \*
        arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
          arr_x_val px_val (⟨(1, 0), 0⟩)%arr \*
          (\*_(d <- interval 0 N)
              arr_x_ind px_ind (⟨(2, 0), d⟩)%arr \*
              arr_x_val px_val (⟨(2, 0), d⟩)%arr)) hv).
Proof.
  intros.
  rewrite -> Union_localization.
  2: apply ind_seg_disjoint.
  eapply xfor_big_op_lemma with
    (Inv:=fun=> arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
      arr_x_val px_val (⟨(1, 0), 0⟩)%arr)
    (R:=fun j => 
      (arr_x_ind px_ind (Lab (2, 0) j) \* arr_x_val px_val (Lab (2, 0) j)))
    (R':=fun j => 
      (arr_x_ind px_ind (Lab (2, 0) j) \* arr_x_val px_val (Lab (2, 0) j)))
    (p:=ps0) (op:=fun hv i => (fset_fold 0
      (fun d acc => acc + (match (hv d) with val_int n => n | _ => 0 end))
      (label (Lab (pair 2 0) (fm_localize (interval 0 M) ind_seg i))))).
  all: match goal with |- context[subst _ _ _ = _] => intros; auto | _ => idtac end.
  all: match goal with |- context[var_eq ?a ?b] => intros; auto | _ => idtac end.
  4-5: math.
  2: apply fm_localization; apply ind_seg_disjoint.
  2:{
    intros. apply fold_fset_eq. intros. extens. intros.
    destruct d as (ll, dd).
    pose proof H0 as Htmp. apply indom_label in Htmp. subst ll.
    rewrite -> H; try reflexivity.
    rewrite indom_label_eq in H0. intuition.
  }
  (* important *)
  (* pre *)
  2:{
    rewrite <- Union_localization.
    2: apply ind_seg_disjoint.
    rewrite <- interval_segmentation.
    xsimpl.
  }
  (* post *)
  2:{
    intros. rewrite <- interval_segmentation at 2. xsimpl.
    rewrite <- Union_localization.
    2: apply ind_seg_disjoint.
    xsimpl.

    match goal with |- himpl (hsingle _ _ ?v) (hsingle _ _ ?v') =>
      enough (v = v') end.
    1:{ rewrite -> H. apply himpl_refl. }

    unfold Sum.
    (* use ext *)
    rewrite -> fold_fset_eq with (f2:=(fun idx : int =>
      Z.add^~ (fset_fold 0
                  (fun d : labeled int =>
                  Z.add^~ match hv d with
                          | val_int n => n
                          | _ => 0
                          end) ⟨(2, 0), ind_seg idx⟩))).
    2:{ intros. extens. intros. f_equal. 
      f_equal.
      unfold fm_localize, uni.
      case_if; eqsolve.
    }
    rewrite <- H_Lind_last, <- segmentation_sum; try math.
  }
  (* main *)
  1:{
    intros l x Hl.

    (* unset localization *)
    unfold fm_localize, uni. rewrite -> indom_interval.
    case_if; try eqsolve.
    destruct Hl as (Hl1 & Hl2).

    apply (xfocus_lemma (pair 2 0)); simpl; try apply xnwp0_lemma.
    rewrite -> union_empty_r.

    (* little change *)
    rewrite -> wp_ht_eq with (ht2:=(fun d => ((rli_func (eld d)) px_ind px_val))).
    2:{ intros. unfolds label. 
      rewrite -> indom_Union in H. 
      setoid_rewrite -> indom_single_eq in H.
      simpl in H.
      destruct H as (? & H & <-).
      simpl. case_if; eqsolve.
    }
    
    (* bundle *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=(\*_(d <- (label (Lab (2, 0) (ind_seg l))))
      arr_x_ind px_ind (Lab (2, 0) (eld d)) \* 
      arr_x_val px_val (Lab (2, 0) (eld d))))
      (Q1:=fun hv =>
        (\*_(d <- (label (Lab (2, 0) (ind_seg l))))
          \[hv d = val_int (nth (abs l) Lval)]) \*
        (\*_(d <- (label (Lab (2, 0) (ind_seg l))))
          (arr_x_ind px_ind (Lab (2, 0) (eld d)) \* 
          arr_x_val px_val (Lab (2, 0) (eld d))))).
    2: xsimpl.
    1:{
      eapply htriple_conseq.
      1: apply htriple_union_pointwise with (Q:=
        fun d hv => 
            \[hv d = val_int (nth (abs l) Lval)] \*
            arr_x_ind px_ind d \* arr_x_val px_val d).
      3: xsimpl.
      2:{
        intros d Hin.
        apply wp_equiv.
        rewrite -> wp_ht_eq with (fs:=(single d tt)) (ht1:=fun d0 => rli_func (eld d0) px_ind px_val) 
          (ht2:=(fun=> ((rli_func (eld d)) px_ind px_val))).
        2:{
          introv HH. rewrite -> indom_single_eq in HH. by subst.
        }
        destruct d as (ll, d). 
        rewrite indom_label_eq in Hin. destruct Hin as (<- & Hin).
        unfold ind_seg in Hin.
        rewrite -> indom_interval in Hin.
        apply wp_equiv. simpl. 
        eapply htriple_conseq. 1: eapply rli_func_spec with (a:=l).
        4: xsimpl. 
        4:{ xsimpl; intros. auto. }
        all: try math.
        destruct Hin as (Hin1 & Hin2). split.
        { rewrite <- H_Lind_first. transitivity (nth (abs l) Lind); auto.
          replace 0%nat with (abs 0%Z) by math. apply H_Lind_inc'; math.
        }
        { rewrite <- H_Lind_last. 
          enough (nth (abs (l + 1)) Lind <= nth (abs M) Lind)%Z by math.
          apply H_Lind_inc'; math.
        }
      }
      1:{ intros. by rewrite -> H. }
      1:{
        xsimpl. intros hv. rewrite -> ! hbig_fset_hstar. xsimpl. 
      }
    }
    xsimpl. intros hv.
    rewrite -> hstar_fset_pure. xsimpl. intros. 

    (* now, only a single thing is left *)
    unfold nwp. simpl. rewrite -> union_empty_r.
    match goal with |- himpl _ (wp _ (htrm_of (cons (Lab _ (FH _ ?ht)) _)) _) => pose (ff:=ht) end.
    rewrite -> wp_ht_eq with (ht2:=ff).
    2:{ 
      intros (ll, d) HH. rewrite indom_label_eq in HH. 
      destruct HH as (<- & HH). 
      subst ff. unfold htrm_of. simpl. case_if; eqsolve.
    }
    subst ff. simpl.

    (* do the body *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=ps0 ~⟨(1%Z, 0%Z), 0⟩~> x \*
      arr_x_val px_val (⟨(1, 0), 0⟩)%arr \* arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr).
    2: xsimpl.
    1:{
      fold (rlsum_loopbody px_ind px_val ps0 l).
      rewrite label_single.
      apply rlsum_loopbody_spec.
      math.
    }
    xsimpl. intros r.
    rewrite -> fold_fset_eq with (f2:=fun _ acc => acc + nth (abs l) Lval).
    2:{
      intros (ll, d) HH. 
      pose proof HH as Htmp. apply indom_label in Htmp. subst ll.
      unfold uni. case_if; try eqsolve. 
      rewrite indom_label_eq in HH. destruct HH as (_ & HH).
      specialize (H _ HH). rewrite H. reflexivity.
    }

    rewrite summation_const_for_rlsum; auto.
    apply H_Lind_inc'; math.
  }
Qed.

Lemma rlsum_rli_ntriple : forall (px_ind px_val : loc),
  ntriple 
    ((\*_(d <- ⟨pair 1 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
     (\*_(d <- ⟨pair 2 0, interval 0 N⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))))
    ((Lab (pair 1 0) (FH (single 0 tt) (fun=> (rlsum_func M px_ind px_val)))) :: 
      (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => \[hv (Lab (pair 1 0) 0) = 
      fset_fold (val_int 0) 
        (fun d acc => val_int_add acc (hv d))
        (label (Lab (pair 2 0) (interval 0 N)))] \*
      (\*_(d <- ⟨pair 1 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
     (\*_(d <- ⟨pair 2 0, interval 0 N⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d)))).
Proof.
  intros.
  unfold rlsum_func.
  (* simplify 1 first *)
  apply (xfocus_lemma (pair 1 0)); simpl; try apply xnwp0_lemma.
  rewrite -> union_empty_r.
  (* little change *)
  rewrite -> wp_ht_eq with (ht2:=(fun=> (rlsum_func M px_ind px_val))).
  2:{ intros (?, ?) H. rewrite label_single indom_single_eq in H. 
    rewrite indom_single_eq. simpl. case_if; eqsolve.
  }
  (* do app2 for rlsum *)
  apply wp_equiv. eapply htriple_eval_like.
  1: apply eval_like_app_fun2; eqsolve.
  (* subst pushdown *)
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  rewrite -> ! For_subst; try eqsolve. 
  (* assign location *)
  eapply htriple_let.
  1:{ 
    rewrite <- hstar_hempty_l at 1.
    eapply htriple_frame. apply htriple_ref.
  }
  intros.
  (* fold *)
  remember (For _ _ _) as ee.
  simpl.
  (* s -> (v d); use funext *)
  match type of Heqee with _ = For _ _ ?b => remember b as body end.
  subst ee.
  replace (fun d : D => (trm_seq (subst "s" (v1 d) (For 0 M body))
      (val_get (v1 d)))) with 
    (fun d : D => (trm_seq (For 0 M (subst "s" (v1 d) body))
      (val_get (v1 d)))).
  2:{ extens. intros. rewrite <- For_subst; try eqsolve. }
  subst body.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  (* simplify hexists *)
  apply wp_equiv.
  xsimpl. intros ps ->. xsimpl.
  (* use only one point location of ps; then forget ps *)
  remember (ps (Lab (1, 0) 0)) as ps0.
  erewrite -> wp_ht_eq with (ht2:=
    fun=> trm_seq (For 0 M (trm_fun "i" (rlsum_loopbody px_ind px_val ps0 "i"))) 
      (trm_let "res" (val_get ps0) (trm_seq (val_free ps0) "res"))).
  2:{ 
    intros. unfolds label, rlsum_loopbody. 
    rewrite -> indom_Union in H. 
    setoid_rewrite -> indom_single_eq in H.
    destruct H as (? & <- & <-).
    simpl. by subst ps0. 
  }
  apply wp_equiv.
  eapply htriple_conseq.
  3: apply qimpl_refl.
  2:{
    apply himpl_frame_l with (H1':=ps0 ~⟨(1%Z, 0%Z), 0⟩~> 0). subst ps0.
    apply himpl_refl.
  }
  clear ps Heqps0.
  apply wp_equiv.
  xunfocus.

  (* SeqU2 *)
  eapply ntriple_sequ2.
  1: math.
  1: rewrite <- interval_segmentation at 2.
  1: apply rlsum_rli_align_step.
  2:{ intros. xsimpl. rewrite -> H. 
    2: rewrite -> indom_union_eq; left. 
    2: rewrite -> indom_label_eq; split; auto.
    intros ->. apply fold_fset_eq.
    intros. extens. intros. rewrite -> H; try reflexivity.
    by rewrite -> indom_union_eq; right.
  }
  intros.
  simpl. 
  eapply htriple_conseq_frame with (Q1:=fun hv2 => \[hv2 = fun=> fset_fold (val_int 0) 
    (fun d acc => val_int_add acc (hv d))
    (label (Lab (pair 2 0) (interval 0 N)))]).
  2: apply himpl_frame_r.
  1:{
    apply wp_equiv. xwp. xlet.
    apply wp_equiv. rewrite label_single.
    eapply htriple_conseq.
    2:{ rewrite <- hbig_fset_label_single' with (Q:=fun d0 => ps0 ~(d0)~> _). xsimpl. }
    1: apply htriple_get.
    xsimpl. intros r ->.
    xwp. xseq. xwp. xapp. xwp. xval. by xsimpl.
  }
  1: xsimpl.
  hnf. intros.
  xsimpl. intros ->.
  unfold uni. rewrite -> indom_label_eq, indom_single_eq. case_if; try eqsolve.
  apply fold_fset_eq.
  intros. extens. intros. case_if; try reflexivity.
  destruct d as (ll, d). apply indom_label in H, C10. eqsolve.
Qed.

Lemma rl_loopbody_spec (d : D) (px px_ind px_val pi0 : loc) (l : int) (v0 : val)
  (Hl : (0 <= l < N)%Z) (a : int) (Ha : (0 <= a < M)%Z)
  (Ha' : (nth (abs a) Lind <= l < nth (abs (a + 1)) Lind)%Z) :
  htriple (single d tt)
    (fun=> rl_loopbody px px_ind px_val pi0 l)
  (pi0 ~(d)~> a \* arr_x_val px_val d \* arr_x_ind px_ind d \*
    (px + 1 + abs l)%nat ~(d)~> v0)
  (fun=> (\exists new_a, \[if Z.eqb l (N-1) then new_a = M else 
    (0 <= new_a < M)%Z /\ (nth (abs new_a) Lind <= l + 1 < nth (abs (new_a + 1)) Lind)%Z] \* 
    pi0 ~(d)~> (val_int new_a)) \* 
    arr_x_val px_val d \* arr_x_ind px_ind d \*
    (px + 1 + abs l)%nat ~(d)~> nth (abs a) Lval).
Proof.
  unfold rl_loopbody.
  apply wp_equiv. xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=pi0 ~(d)~> a).
  2: xsimpl.
  1:{
    rewrite <- hbig_fset_label_single' with (Q:=fun d0 => pi0 ~(d0)~> a).
    apply htriple_get.
  }
  xsimpl. intros ? ->.
  xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=arr_x_val px_val d).
  1:{
    rewrite <- hbig_fset_label_single' with (Q:=fun d0 => arr_x_val px_val d0).
    eapply htriple_array_get.
    { intros. rewrite -> length_map, -> H_length_Lval. math. }
    { intros. reflexivity. } 
  }
  1: xsimpl.
  xsimpl. intros r Er.
  xwp. xseq.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=(px + 1 + abs l)%nat ~(d)~> v0).
  1:{
    rewrite <- hbig_fset_label_single' with (Q:=fun d0 => (px + 1 + abs l)%nat ~(d0)~> v0).
    eapply htriple_array_set_pre.
    intros; math.
  }
  1: xsimpl.
  xsimpl. 
  xwp. xlet. xapp.
  xwp. xlet. xapp.
  xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=arr_x_ind px_ind d).
  1:{
    rewrite <- hbig_fset_label_single' with (Q:=fun d0 => arr_x_ind px_ind d0).
    eapply htriple_array_get.
    { intros. rewrite -> length_map, -> H_length_Lind. math. }
    { intros. reflexivity. } 
  }
  1: xsimpl.
  xsimpl. intros r0 Er0.
  specialize (Er _ (indom_single d _)).
  specialize (Er0 _ (indom_single d _)).
  rewrite -> wp_ht_eq with (ht2:=fun=> 
  let aa := r0 d in let bb := Z.add l 1 in let cc := rli_whilebody (trm_val (val_loc pi0)) in
    <{
       let "cmp" = bb >= aa in
       if "cmp" then cc end }>).
  2:{ intros. rewrite -> indom_single_eq in H. subst. by simpl. }
  simpl. rewrite -> Er0.
  rewrite -> ! nth_map; try math.
  xwp. xlet. xapp. xwp. xif; intros Hcmp.
  { (* next phase *)
    assert (l + 1 = nth (abs (a + 1)) Lind) by math.
    fold (rli_whilebody (trm_val (val_loc pi0))).
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=(\*_(d0 <- single d tt) pi0 ~(d0)~> a)).
    1:{
      rewrite hbig_fset_label_single'.
      apply wp_equiv, rli_whilebody_spec.
    }
    1: xsimpl.
    xsimpl.
    2: rewrite ! hbig_fset_label_single'; xsimpl; rewrite -> Er, -> nth_map.
    2: xsimpl.
    2: math.

    (* pure proof *)
    destruct (l =? N - 1)%Z eqn:E.
    { rewrite -> Z.eqb_eq in E.
      subst l. replace (N-1+1) with N in H by math.
      destruct (Z.leb M (a+1)) eqn:E'.
      { rewrite -> Z.leb_le in E'. math. }
      { rewrite -> Z.leb_gt in E'. 
        assert (abs (a+1) < abs M)%nat as EE by math.
        apply H_Lind_inc in EE; math.
      }
    }
    { rewrite -> Z.eqb_neq in E.
      assert (l < N - 1) as El by math.
      destruct (Z.leb M (a+1)) eqn:E'.
      { rewrite -> Z.leb_le in E'. 
        assert (a + 1 = M) as Eap by math.
        rewrite -> Eap, -> H_Lind_last in H. math.
      }
      { rewrite -> Z.leb_gt in E'.
        split; try math.
        split; try math.
        rewrite -> H. apply H_Lind_inc; math.
      }
    }
  }
  {
    xwp. xval. xsimpl.
    2: rewrite ! hbig_fset_label_single'; xsimpl; rewrite -> Er, -> nth_map.
    2: xsimpl.
    2: math.

    destruct (l =? N - 1)%Z eqn:E. 2: intuition math.
    rewrite -> Z.eqb_eq in E. subst l. replace (N-1+1) with N in Hcmp by math.
    false Hcmp. rewrite <- H_Lind_last. 
    enough (nth (abs (a + 1)) Lind <= nth (abs M) Lind)%Z by math.
    apply H_Lind_inc'; math.
  }
Qed.

Lemma rl_rli_align_step : forall (px_ind px_val : loc) (pi0 px : loc),
  ntriple 
    (pi0 ~⟨(3%Z, 0%Z), 0⟩~> 0 \*
      (* harray (LibList.make (abs N) val_uninit) px (⟨(2, 0), 0⟩)%arr \* *)
      hcells (LibList.make (abs N) val_uninit) (px + 1)%nat (⟨(3, 0), 0⟩)%arr \*
      (\*_(d <- ⟨pair 3 0, single 0 tt⟩) 
        ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
      (\*_(d <- ⟨pair 4 0, interval 0 N⟩) 
        ((arr_x_ind px_ind d) \* (arr_x_val px_val d))))
    ((Lab (pair 3 0) 
        (FH (single 0 tt) (fun=> 
          For 0 N (trm_fun "k" (rl_loopbody (val_loc px) (val_loc px_ind) (val_loc px_val) (val_loc pi0) "k"))
          ))) :: 
      (Lab (pair 4 0) 
        (FH (Union (interval 0 N) (fun i => single i tt)) 
          (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => 
      (@hexists (list val) (fun Larr =>
        \[length Larr = abs N] \* (\*_(d <- ⟨pair 4 0, interval 0 N⟩) 
           \[hv d = nth (abs (eld d)) Larr]) \*
        (* harray (LibList.map val_int Larr) px (Lab (pair 2 0) 0))) \*  *)
        hcells Larr (px + 1)%nat (⟨(3, 0), 0⟩)%arr)) \*
        pi0 ~⟨(3%Z, 0%Z), 0⟩~> M \*
        (\*_(d <- ⟨pair 3 0, single 0 tt⟩) 
          ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
        (\*_(d <- ⟨pair 4 0, interval 0 N⟩) 
          ((arr_x_ind px_ind d) \* (arr_x_val px_val d)))).
Proof.
  intros.
  eapply xfor_specialized_lemma with
    (* have to count for i = N *)
    (Inv:=fun i => (@hexists int (fun a => 
      \[if (Z.leb N i) 
        then a = M 
        else (0 <= a < M)%Z /\ (nth (abs a) Lind <= i < nth (abs (a + 1)) Lind)%Z] \* 
      pi0 ~⟨(3%Z, 0%Z), 0⟩~> val_int a)) \*
      arr_x_ind px_ind (⟨(3, 0), 0⟩)%arr \*
      arr_x_val px_val (⟨(3, 0), 0⟩)%arr)
    (R:=fun j => 
      (arr_x_ind px_ind (Lab (4, 0) j) \* arr_x_val px_val (Lab (4, 0) j)))
    (R':=fun j => 
      (arr_x_ind px_ind (Lab (4, 0) j) \* arr_x_val px_val (Lab (4, 0) j)))
    (p:=fun i => ((px + 1)%nat + abs i)%nat).
  all: match goal with |- context[subst _ _ _ = _] => intros; auto | _ => idtac end.
  all: match goal with |- context[var_eq ?a ?b] => intros; auto | _ => idtac end.
  3: math.
  3: apply zero_le_N.
  2:{ intros. by apply disjoint_single_single. }
  (* pre *)
  2:{
    xsimpl.
    1:{
      pose proof zero_lt_N as Htmp. rewrite <- Z.leb_gt in Htmp.
      rewrite -> Htmp. 
      split; try math.
      split. 1: change (abs 0) with 0%nat; by rewrite -> H_Lind_first.
      replace (0+1) with 1 by math. rewrite <- H_Lind_first. 
      change 0%nat with (abs 0).
      apply H_Lind_inc; math.
    }
    xsimpl.
    rewrite -> ! interval_point_segmentation.
    xsimpl.
    rewrite -> hcells_form_transform with (L:=N) (Larr:=(LibList.make (abs N) val_uninit)); 
      try math.
    2: apply zero_le_N.
    2: by rewrite -> length_make.
    1: apply himpl_refl.
    intros. apply nth_make. math.
  }
  (* post *)
  2:{
    intros. 
    (* prepare *)
    destruct (list_from_map (fun d => hv (Lab (4, 0) d)) (abs N)) as 
      (Larr & Hlen & Hcorr).
    xsimpl. instantiate (1:=Larr). 1: auto.
    intros a H. 
    rewrite -> Z.leb_refl in H. subst a.
    rewrite -> ! interval_point_segmentation.
    rewrite -> hcells_form_transform with (L:=N) (Larr:=Larr); 
      try math.
    2: apply zero_le_N.
    2: intros; rewrite Hcorr; auto.
    xsimpl. 
    rewrite -> hstar_fset_pure. xsimpl. 
    intros. rewrite -> indom_interval in H. rewrite -> Hcorr; auto; try math.
  }
  (* main *)
  {
    intros l (Hl1 & Hl2).
    apply (xfocus_lemma (pair 4 0)); simpl; try apply xnwp0_lemma.
    rewrite -> union_empty_r.

    (* reusing the part above. *)
    (* little change *)
    rewrite -> wp_ht_eq with (ht2:=(fun=> ((rli_func l) px_ind px_val))).
    2:{ intros. unfolds label. 
      rewrite -> indom_Union in H. 
      setoid_rewrite -> indom_single_eq in H.
      simpl in H.
      destruct H as (? & H & <-).
      simpl. 
      rewrite indom_single_eq. case_if; eqsolve.
    }

    (* extract *)
    xsimpl. intros a Ha.
    assert (l < N)%Z as Htmp by math. rewrite <- Z.leb_gt in Htmp.
    rewrite -> Htmp in Ha. clear Htmp.
    destruct Ha as ((Ha1 & Ha2) & (Hl1' & Hl2')).
    
    (* a single element here, so very easy *)
    apply wp_equiv.
    eapply htriple_conseq_frame.
    1:{
      rewrite label_single.
      apply rli_func_spec with (a:=a); math. 
    }
    1: xsimpl.
    xsimpl. intros r Er.

    (* now, only a single thing is left *)
    unfold nwp. simpl. rewrite -> union_empty_r.
    match goal with |- himpl _ (wp _ (htrm_of (cons (Lab _ (FH _ ?ht)) _)) _) => pose (ff:=ht) end.
    rewrite -> wp_ht_eq with (ht2:=ff).
    2:{ 
      intros (ll, d) HH. rewrite indom_label_eq in HH. 
      destruct HH as (<- & HH). 
      subst ff. unfold htrm_of. simpl. case_if; eqsolve.
    }
    subst ff. simpl.

    (* do the body *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pi0 ~⟨(3%Z, 0%Z), 0⟩~> a \* 
      arr_x_val px_val (⟨(3, 0), 0⟩)%arr \* arr_x_ind px_ind (⟨(3, 0), 0⟩)%arr \*
      ((px + 1)%nat + abs l)%nat ~⟨(3%Z, 0%Z), 0⟩~> val_uninit).
    2: xsimpl.
    1:{
      rewrite label_single.
      apply rl_loopbody_spec; math.
    }
    xsimpl. 
    {
      intros. destruct (l =? N - 1)%Z eqn:E.
      { rewrite -> Z.eqb_eq in E.
        assert (N <= l + 1)%Z as Htmp by math.
        rewrite <- Z.leb_le in Htmp. by rewrite Htmp.
      }
      { rewrite -> Z.eqb_neq in E.
        assert (l + 1 < N)%Z as Htmp by math.
        rewrite <- Z.leb_gt in Htmp. by rewrite Htmp.
      }
    }
    {
      intros. unfold uni. rewrite label_single indom_single_eq.
      case_if. rewrite Er. xsimpl.
    }
  }
Qed.

Lemma rl_rli_ntriple : forall (px_ind px_val : loc),
  ntriple 
    ((\*_(d <- ⟨pair 3 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
      (\*_(d <- ⟨pair 4 0, interval 0 N⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))))
    ((Lab (pair 3 0) (FH (single 0 tt) (fun=> (rl_func N px_ind px_val)))) :: 
      (Lab (pair 4 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => 
      (@hexists loc (fun px => \[(hv (Lab (pair 3 0) 0)) = val_loc px] \*
        (@hexists (list val) (fun Larr =>
        \[length Larr = (abs N)] \* 
        (\*_(d <- ⟨pair 4 0, interval 0 N⟩) \[hv d = (nth (abs (eld d)) Larr)]) \*
        harray Larr px (Lab (pair 3 0) 0))))) \* 
        (\*_(d <- ⟨pair 3 0, single 0 tt⟩) 
          ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
        (\*_(d <- ⟨pair 4 0, interval 0 N⟩) 
          ((arr_x_ind px_ind d) \* (arr_x_val px_val d)))).
Proof.
  intros.
  unfold rl_func.
  (* simplify 1 first *)
  apply (xfocus_lemma (pair 3 0)); simpl; try apply xnwp0_lemma.
  rewrite -> union_empty_r.
  (* little change *)
  rewrite -> wp_ht_eq with (ht2:=(fun=> (rl_func N px_ind px_val))).
  2:{ 
    intros (ll, d) H. rewrite indom_label_eq indom_single_eq in H.
    destruct H as (<- & <-).
    simpl. rewrite -> indom_single_eq. case_if; auto.
  }
  (* do app2 for rlsum *)
  apply wp_equiv. eapply htriple_eval_like.
  1: apply eval_like_app_fun2; eqsolve.
  (* subst pushdown *)
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  rewrite -> ! For_subst; try eqsolve.
  (* array allocation *)
  apply wp_equiv. xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=\[]).
  1: apply htriple_alloc_nat.
  1: xsimpl.
  xsimpl. intros r. xsimpl. intros px Er.
  xwp. xlet. xwp. xapp.
  intros pi. xsimpl.
  (* single point forget *)
  remember (pi[3](0)) as pi0.
  erewrite -> wp_ht_eq with (ht2:=
    fun=> trm_seq (For 0 N (trm_fun "k" (rl_loopbody px px_ind px_val pi0 "k"))) 
      (trm_seq (val_free pi0) px)).
  2:{ 
    intros (ll, d) H. rewrite indom_label_eq indom_single_eq in H.
    destruct H as (<- & <-).
    unfold For, For_aux, rl_loopbody, rli_whilebody. 
    by rewrite -> Er, Heqpi0.
  }
  apply wp_equiv.
  eapply htriple_conseq.
  3: apply qimpl_refl.
  2:{
    apply himpl_frame_l with (H1':=pi0 ~⟨(3%Z, 0%Z), 0⟩~> 0). subst pi0.
    apply himpl_refl.
  }
  clear pi Heqpi0 r Er.
  apply wp_equiv.
  xunfocus.

  (* SeqU2 *)
  eapply ntriple_sequ2.
  1: math.
  1: rewrite <- interval_point_segmentation at 2.
  1:{
    unfold harray.
    apply wp_equiv. eapply htriple_conseq_frame.
    1: apply wp_equiv, rl_rli_align_step.
    1:{
      rewrite -> ! hstar_assoc. xsimpl.
      rewrite -> hstars_pick_last_3 at 1. xsimpl.
    }
    apply qimpl_refl.
  }
  1:{
    (* delicate control ... *)
    intros. apply wp_equiv. xwp. xseq.
    xsimpl. intros Larr Hlen.
    rewrite -> hstar_fset_pure. 
    xsimpl. intros Hcorr.
    apply wp_equiv. rewrite label_single.
    eapply htriple_conseq_frame with (H1:=pi0 ~⟨(3%Z, 0%Z), 0⟩~> M).
    1:{ rewrite <- hbig_fset_label_single' with (Q:=fun d0 => pi0 ~(d0)~> M).
      apply htriple_free.
    }
    1: xsimpl.
    xsimpl. xwp. xval.
    rewrite <- hstars_pick_last_4.
    rewrite -> hstar_assoc at 1.
    rewrite -> hstars_pick_last_4.
    apply himpl_frame_lr. 2: xsimpl.
    apply himpl_hexists_r with (x:=px).
    apply himpl_hstar_hpure_r. 
    1:{
      unfold uni. rewrite indom_single_eq. case_if; eqsolve.
    }
    apply himpl_hexists_r with (x:=Larr).
    unfold harray. xsimpl; auto.
    rewrite -> hstar_fset_pure.
    xsimpl.
    2: by rewrite -> length_make, -> Hlen.
    intros. unfold uni. rewrite indom_single_eq. 
    case_if; try eqsolve. rewrite Hcorr; auto.
  }
  {
    intros. apply himpl_frame_lr.
    2: xsimpl.
    apply himpl_hexists_l. intros pxx.
    apply himpl_hexists_r with (x:=pxx).
    xsimpl; auto.
    { intros. rewrite <- H; auto.
      rewrite indom_union_eq ! indom_label_eq indom_single_eq.
      intuition.
    }
    { intros.
      apply hbig_fset_himpl. 
      intros. xsimpl. intros HH. rewrite <- HH, -> H; auto.
      rewrite indom_union_eq ! indom_label_eq indom_single_eq.
      tauto.
    }
  }
Qed.

(* a basic composition *)
Lemma rlsum_rl_rli_ntriple_pre : forall (px_ind px_val : loc),
  ntriple 
    (((\*_(d <- ⟨pair 1 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
     (\*_(d <- ⟨pair 2 0, interval 0 N⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d)))) \*
      (\*_(d <- ⟨pair 3 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
      (\*_(d <- ⟨pair 4 0, interval 0 N⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))))
    ((Lab (pair 1 0) (FH (single 0 tt) (fun=> (rlsum_func M px_ind px_val)))) :: 
    (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
      (Lab (pair 3 0) (FH (single 0 tt) (fun=> (rl_func N px_ind px_val)))) :: 
      (Lab (pair 4 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => 
      (\[hv (Lab (pair 1 0) 0) = 
      fset_fold (val_int 0) 
        (fun d acc => val_int_add acc (hv d))
        (label (Lab (pair 2 0) (interval 0 N)))] \*
        (\*_(d <- ⟨pair 1 0, single 0 tt⟩) 
          ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
        (\*_(d <- ⟨pair 2 0, interval 0 N⟩) 
          ((arr_x_ind px_ind d) \* (arr_x_val px_val d)))
      ) \*
      (@hexists loc (fun px => \[(hv (Lab (pair 3 0) 0)) = val_loc px] \*
        (@hexists (list val) (fun Larr =>
        \[length Larr = (abs N)] \* 
        (\*_(d <- ⟨pair 4 0, interval 0 N⟩) \[hv d = (nth (abs (eld d)) Larr)]) \*
          harray Larr px (Lab (pair 3 0) 0))))) \* 
        (\*_(d <- ⟨pair 3 0, single 0 tt⟩) 
          ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
        (\*_(d <- ⟨pair 4 0, interval 0 N⟩) 
          ((arr_x_ind px_ind d) \* (arr_x_val px_val d)))).
Proof.
  intros.
  unfold nwp. apply wp_equiv. 
  simpl fset_of. rewrite -> union_empty_r.
  rewrite <- union_assoc.
  apply htriple_union.
  1:{
    apply disjoint_of_not_indom_both.
    intros (l, d). rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq ! indom_interval.
    intros [ ? | ? ] [ ? | ? ]; eqsolve.
  }
  1:{
    intros. xsimpl. intros. rewrite <- H.
    2: rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq ! indom_interval; tauto.
    rewrite H0. apply fold_fset_eq.
    intros. extens. intros. rewrite H; auto.
    destruct d.
    rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq ! indom_interval.
    rewrite ! indom_label_eq indom_interval in H1.
    tauto.
  }
  1:{
    intros. xsimpl.
    { intros. rewrite <- H0. symmetry.
      apply H. 
      rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq ! indom_interval.
      tauto.
    }
    { intros. auto. }
    { intros.
      apply hbig_fset_himpl. 
      intros. xsimpl. intros HH. rewrite <- HH, -> H; auto.
      rewrite indom_union_eq ! indom_label_eq indom_single_eq.
      tauto.
    }
  }
  1:{
    remember ((Lab (pair 1 0) (FH (single 0 tt) (fun=> (rlsum_func M px_ind px_val)))) :: 
      (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: nil) as lsq.
    match goal with |- htriple ?fs _ _ _ => replace fs with (fset_of lsq) end.
    2:{ subst. simpl. by rewrite -> union_empty_r. } 
    apply wp_equiv.
    rewrite -> wp_ht_eq with (ht2:=htrm_of lsq).
    2:{ 
      subst. simpl. intros (l, d). rewrite -> union_empty_r. 
      unfold htrm_of.
      rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq ! indom_interval.
      intros [ ? | ? ]; repeat case_if; eqsolve.
    }
    subst lsq. apply rlsum_rli_ntriple.
  }
  1:{
    remember ((Lab (pair 3 0) (FH (single 0 tt) (fun=> (rl_func N px_ind px_val)))) :: 
      (Lab (pair 4 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: nil) as lsq.
    match goal with |- htriple ?fs _ _ _ => replace fs with (fset_of lsq) end.
    2:{ subst. simpl. by rewrite -> union_empty_r. } 
    apply wp_equiv.
    rewrite -> wp_ht_eq with (ht2:=htrm_of lsq).
    2:{ 
      subst. simpl. intros (l, d). rewrite -> union_empty_r. 
      unfold htrm_of.
      rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq ! indom_interval.
      intros [ ? | ? ]; repeat case_if; eqsolve.
    }
    subst lsq. apply rl_rli_ntriple.
  }
Qed.

(* a better composition *)
Lemma rlsum_rl_rli_ntriple : forall (px_ind px_val : loc),
  ntriple 
    ((\*_(d <- ⟨pair 1 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
      (\*_(d <- ⟨pair 2 0, interval 0 N⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
      (\*_(d <- ⟨pair 3 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))))
    ((Lab (pair 1 0) (FH (single 0 tt) (fun=> (rlsum_func M px_ind px_val)))) :: 
      (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) ::
      (Lab (pair 3 0) (FH (single 0 tt) (fun=> (rl_func N px_ind px_val)))) ::  
      nil)
    (fun hv => 
      (@hexists loc (fun px => \[(hv (Lab (pair 3 0) 0)) = val_loc px] \*
        (@hexists (list val) (fun Larr =>
        \[length Larr = (abs N) /\
        hv (Lab (pair 1 0) 0) = fold_left val_int_add (val_int 0) Larr] \* 
        harray Larr px (Lab (pair 3 0) 0))))) \* 
        hhtop (⟨(1, 0), single 0 tt⟩ \u ⟨(2, 0), interval 0 N⟩ \u ⟨(3, 0), single 0 tt⟩)).
Proof.
  intros.
  match goal with |- ntriple _ ?ls _ => remember ls as lsq' eqn:E' end.
  unfold ntriple, nwp. apply wp_equiv.
  (* the original lsq *)
  remember ((Lab (pair 1 0) (FH (single 0 tt) (fun=> (rlsum_func M px_ind px_val)))) :: 
    (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
    (Lab (pair 3 0) (FH (single 0 tt) (fun=> (rl_func N px_ind px_val)))) :: 
    (Lab (pair 4 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
    nil) as lsq eqn:E.
  pose (f := fun (d : D) => 
    If indom (label (Lab (4, 0) (interval 0 N))) d
    then (Lab (2, 0) (eld d))
    else d).
  pose (g := fun (d : D) => 
    If indom (label (Lab (4, 0) (interval 0 N))) d
    then (Lab (5, 0) 0)
    else d).
  (* use a good layout *)
  pose proof (fun x => iff_refl (indom (fset_of lsq) x)) as Hindom.
  pose proof (fun ll d => iff_refl (indom (fset_of lsq) (Lab ll d))) as Hindom'.
  setoid_rewrite E in Hindom' at 1.
  unfold fset_of in Hindom' at 1.
  simpl in Hindom'. 
  setoid_rewrite union_empty_r in Hindom'.
  repeat setoid_rewrite indom_union_eq in Hindom'.
  repeat setoid_rewrite indom_label_eq in Hindom'.
  repeat setoid_rewrite indom_single_eq in Hindom'.
  assert (fsubst (fset_of lsq) f = fset_of lsq') as Efs.
  { subst lsq lsq'. simpl. rewrite ! union_empty_r.
    (* prove by def *)
    apply fset_extens.
    intros (ll, d). 
    rewrite indom_fsubst.
    transitivity (exists ll' d', f (Lab ll' d') = (⟨ll, d⟩)%arr /\
      indom (⟨(1, 0), single 0 tt⟩ \u
      ⟨(2, 0), interval 0 N⟩ \u
      ⟨(3, 0), single 0 tt⟩ \u ⟨(4, 0), interval 0 N⟩) (Lab ll' d')).
    { split. 
      { intros ((?, ?) & H). eauto. }
      { intros (? & ? & H). eauto. }
    }
    rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq.
    subst f. simpl.
    repeat setoid_rewrite indom_union_eq.
    (* repeat setoid_rewrite indom_label_eq.
    repeat setoid_rewrite indom_single_eq. *)
    split.
    { intros (ll' & d' & H).
       rewrite ! indom_label_eq ! indom_single_eq in H.
      repeat case_if; try eqsolve.
      { destruct C. subst ll'. destruct H as (HH & H). inversion HH; subst ll d.
        eqsolve.
      }
      { destruct H as (HH & H). inversion HH; subst ll d.
        eqsolve.
      }
    }
    { intros. intuition; try subst ll d.
      { exists (1, 0) 0. rewrite ! indom_label_eq ! indom_single_eq. repeat case_if; eqsolve. }
      { subst ll. exists (4, 0) d. rewrite ! indom_label_eq ! indom_single_eq. repeat case_if; eqsolve. }
      { exists (3, 0) 0. rewrite ! indom_label_eq ! indom_single_eq. repeat case_if; eqsolve. }
    }
  }
  assert (forall d, indom (fset_of lsq) d -> (htrm_of lsq) d = (htrm_of lsq' \o f) d) as Eht.
  { subst lsq lsq'. unfold htrm_of. intros (ll, d) Hid.
    rewrite <- Hindom' in Hid. 
    subst f. simpl.
    rewrite ! indom_label_eq ! indom_single_eq. 
    repeat case_if; simpl; try eqsolve.
  }

  eapply htriple_conseq_frame with (H2:=\[]).
  1:{
    rewrite <- Efs.
    (* sub *)
    eapply htriple_hsub with (g:=g).
    5:{
      apply wp_equiv. erewrite wp_ht_eq.
      (* use the larger triple *)
      1:{ subst lsq. apply rlsum_rl_rli_ntriple_pre. }
      intros. by rewrite Eht.
    }
    2:{
      intros. simpl.
      assert (forall ll d, indom (fset_of lsq) (Lab ll d) -> hv (Lab ll d) = hv' (Lab ll d)) as H'.
      { intros. by rewrite H. }
      setoid_rewrite <- Hindom' in H'.
      xsimpl; intros.
      {
        specialize (H' (1, 0) 0).
        rewrite H' in H0. 2: eqsolve.
        rewrite H0. apply fold_fset_eq.
        intros (?, ?) Htt. rewrite indom_label_eq in Htt. extens. intros. rewrite H; auto.
        apply Hindom'. eqsolve.
      }
      {
        rewrite <- H1. symmetry. apply H'. eqsolve.
      }
      { auto. }
      { 
        apply hbig_fset_himpl. 
        intros. xsimpl. intros HH. rewrite <- HH.
        symmetry. apply H'. eqsolve.
      }
      {
        specialize (H' (1, 0) 0).
        rewrite H'. 2: eqsolve.
        rewrite H0. apply fold_fset_eq.
        intros (?, ?) Htt. rewrite indom_label_eq in Htt. extens. intros. rewrite H; auto.
        apply Hindom'. eqsolve.
      }
      {
        rewrite <- H1. apply H'. eqsolve.
      }
      { auto. }
      { 
        apply hbig_fset_himpl. 
        intros. xsimpl. intros HH. rewrite <- HH.
        apply H'. eqsolve.
      }
    }
    2:{
      subst f. simpl.
      intros (ll, d) (ll', d') H HH.
      rewrite ! indom_label_eq in HH.
      rewrite <- ! Hindom'.
      repeat case_if; try eqsolve.
      all: inversion HH; simpl in *; try subst ll; try subst ll'; try subst d; try subst d'.
      all: try eqsolve.
    }
    all: rewrite Efs.
    { intros (ll, d) H. subst lsq'. unfold fset_of in H. simpl in H.
      rewrite union_empty_r in H.
      rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq in H.
      subst f g. simpl. 
      repeat case_if; try eqsolve; simpl.
      { rewrite ! indom_label_eq in C, C0. eqsolve. }
      { rewrite ! indom_label_eq in C0. eqsolve. }
    }
    { intros (ll, d). 
      destruct (g (Lab ll d)) as (ll', d') eqn:EE.
      rewrite <- Hindom'.
      subst lsq'. unfold fset_of. simpl.
      rewrite union_empty_r.
      rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq.
      subst g. simpl in EE. rewrite indom_label_eq in EE.
      case_if.
      { inversion EE; subst ll' d'. destruct C as (<- & ?). eqsolve. }
      { inversion EE; subst ll' d'. eqsolve. }
    }
  }
  (* pre sub *)
  {
    rewrite hstar_hempty_r.
    rewrite -> hstar_comm with (H1:=(\*_(d <- ⟨(3, 0), single 0 tt⟩)
      arr_x_ind px_ind d \* arr_x_val px_val d)).
    rewrite hstar_assoc. 
    rewrite <- hstar_assoc with (H2:=(\*_(d <- ⟨(4, 0), interval 0 N⟩)
      arr_x_ind px_ind d \* arr_x_val px_val d)).
    rewrite -> hsub_hstar_id_l with (fs:=⟨(1, 0), single 0 tt⟩).
    1: apply himpl_frame_r.
    4:{ rewrite label_single. rewrite -> hbig_fset_label_single'.
      hlocal. all: apply hlocal_harray.
    }
    2:{
      intros (ll, d). rewrite label_single indom_single_eq. intros <-.
      subst f. simpl. rewrite indom_label_eq. case_if; eqsolve.
    }
    2:{
      subst f. simpl.
      intros (ll, d) (ll', d') H HH.
      rewrite ! indom_label_eq in HH.
      rewrite ! label_single ! indom_single_eq. 
      repeat case_if; try eqsolve.
    }

    rewrite -> hsub_hstar_id_r with (fs:=⟨(3, 0), single 0 tt⟩).
    1: apply himpl_frame_l.
    4:{ rewrite label_single. rewrite -> hbig_fset_label_single'.
      hlocal. all: apply hlocal_harray.
    }
    2:{
      intros (ll, d). rewrite label_single indom_single_eq. intros <-.
      subst f. simpl. rewrite indom_label_eq. case_if; eqsolve.
    }
    2:{
      subst f. simpl.
      intros (ll, d) (ll', d') H HH.
      rewrite ! indom_label_eq in HH.
      rewrite ! label_single ! indom_single_eq. 
      repeat case_if; try eqsolve.
    }

    (* decomposite; matching *)
    rewrite ! hstar_fset_Lab.
    rewrite <- hbig_fset_hstar.
    erewrite hsub_hstar_fset_squash with (fsi:=fun d : int => 
      single (Lab (2, 0) d) tt \u single (Lab (4, 0) d) tt).
    3:{
      intros (lx, dx) (ly, dy). intros.
      rewrite -> indom_union_eq, -> ! indom_single_eq in H2, H3.
      subst f. simpl.
      rewrite ! indom_label_eq. 
      (repeat case_if); destruct H2, H3; try eqsolve.
    }
    2:{
      intros. hlocal. all: (apply hlocal_union_l) + (apply hlocal_union_r); apply hlocal_harray.
    }

    apply hbig_fset_himpl.
    intros.
    (* get some pure thing *)
    unfold arr_x_ind, arr_x_val, harray, hheader. 
    simpl. rewrite -> ! length_map, -> ! H_length_Lind, -> ! H_length_Lval.
    xsimpl. intros NN1 NN2. unfold null in NN1, NN2.
    (* hack *)
    assert (px_ind <> 0%nat) as Hn1 by (intros ->; by apply NN1).
    assert (px_val <> 0%nat) as Hn2 by (intros ->; by apply NN2).
    remember (\[(px_ind, (⟨(2, 0), d⟩)%arr) <> null (⟨(2, 0), d⟩)%arr] \*
      \[(px_val, (⟨(2, 0), d⟩)%arr) <> null (⟨(2, 0), d⟩)%arr] \*
      \[(px_ind, (⟨(4, 0), d⟩)%arr) <> null (⟨(4, 0), d⟩)%arr] \*
      \[(px_val, (⟨(4, 0), d⟩)%arr) <> null (⟨(4, 0), d⟩)%arr] \*
      (px_ind ~⟨(2%Z, 0%Z), d⟩~> val_header (abs (M + 1)) \*
        px_ind ~⟨(4%Z, 0%Z), d⟩~> val_header (abs (M + 1))) \*
      (hcells (LibList.map val_int Lind) (px_ind + 1)%nat (⟨(2, 0), d⟩)%arr \*
        hcells (LibList.map val_int Lind) (px_ind + 1)%nat (⟨(4, 0), d⟩)%arr) \*
      (px_val ~⟨(2%Z, 0%Z), d⟩~> val_header (abs M) \*
        px_val ~⟨(4%Z, 0%Z), d⟩~> val_header (abs M)) \*
      (hcells (LibList.map val_int Lval) (px_val + 1)%nat (⟨(2, 0), d⟩)%arr \*
        hcells (LibList.map val_int Lval) (px_val + 1)%nat (⟨(4, 0), d⟩)%arr)
    ) as Htarg.
    match goal with |- context[hsub ?Hsrc _] => assert (Hsrc = Htarg) as Htmp end.
    1: subst Htarg; xsimpl; auto.
    rewrite Htmp. clear Htmp. subst Htarg.
    rewrite ! hsub_hpure_comm.
    xsimpl.
    1-4: unfold null; simpl; eqsolve.

    (* block-ize *)
    rewrite <- ! hcells_form_transform with (Larr:=(LibList.map val_int Lind)) (L:=M+1)
      (hv:=fun i => val_int (nth (abs i) Lind)); try math.
    2,4: by rewrite length_map.
    2-3: intros; rewrite nth_map; try math.
    rewrite <- ! hcells_form_transform with (Larr:=(LibList.map val_int Lval)) (L:=M)
      (hv:=fun i => val_int (nth (abs i) Lval)); try math.
    2,4: by rewrite length_map.
    2-3: intros; rewrite nth_map; try math.

    pose (pind:=fun i => (px_ind + abs i)%nat).
    (* pose (vind:=fun i => if Z.leb i 0%Z   *)
    pose (vind:=fun i => If i <= 0
      then val_header (abs (M + 1)) 
      else nth (abs (i - 1)) Lind).
    pose (pval:=fun i => (px_val + abs i)%nat).
    (* pose (vval:=fun i => if Z.leb i 0%Z   *)
    pose (vval:=fun i => If i <= 0
      then val_header (abs M)
      else nth (abs (i - 1)) Lval).
    (* pose (pall:=fun i => if Z.leb i (M+1) then pind i else pval (i-(M+2))). *)
    pose (pall:=fun i => If i <= (M+1) then pind i else pval (i-(M+2))).
    (* pose (vall:=fun i => if Z.leb i (M+1) then vind i else vval (i-(M+2))). *)
    pose (vall:=fun i => If i <= (M+1) then vind i else vval (i-(M+2))).
    assert (forall d, indom (interval 0 N) d -> f[2](d) = (Lab (2, 0) d)) as Hid2.
    { subst f. simpl. intros. rewrite indom_label_eq. case_if; eqsolve. }
    assert (forall d, indom (interval 0 N) d -> f[4](d) = (Lab (2, 0) d)) as Hid4.
    { subst f. simpl. intros. rewrite indom_label_eq. case_if; eqsolve. }
    eapply himpl_trans. 2: eapply himpl_trans.
    2: apply hsub_hsingle_groupmerge_himpl with 
      (p:=pall) (v:=vall) (d1:=(Lab (2, 0) d)) (d2:=(Lab (4, 0) d))
      (f:=f) (fs:=interval 0 (M+M+3)).
    2: eqsolve.
    2: by rewrite Hid2.
    2: by rewrite Hid4.
    2:{
      intros (l0, d0) H0.
      subst f. simpl in H0. 
      rewrite indom_label_eq in H0. case_if; try eqsolve.
    }
    2:{
      intros (l0, d0) H0.
      subst f. simpl in H0. 
      rewrite indom_label_eq in H0. case_if; try eqsolve.
      inversion H0. subst l0 d0. eqsolve.
    }
    {
      rewrite -> intervalU with (x:=0) (y:=M+M+3).
      2: math.
      rewrite hbig_fset_update; try assumption.
      3-4: auto.
      2: rewrite indom_interval; intros ?; math.
      rewrite <- interval_union with (x:=0+1) (z:=M+M+3) (y:=M+2); try math.
      rewrite hbig_fset_union; try assumption.
      2-4: hnf; auto.
      2:{
        apply disjoint_of_not_indom_both.
        intros ?. rewrite ! indom_interval. intros; math.
      }
      rewrite <- interval_union with (x:=M+2) (z:=M+M+3) (y:=M+3); try math.
      rewrite hbig_fset_union; try assumption.
      2-4: hnf; auto.
      2:{
        apply disjoint_of_not_indom_both.
        intros ?. rewrite ! indom_interval. intros; math.
      }
      replace (M+2) with ((M+1)+1) at 1 by math.
      replace (M+2) with (0+(M+2)) by math.
      replace (M+3) with (1+(M+2)) at 1 by math.
      replace (M+3) with (0+(M+3)) at 1 by math.
      replace (M+M+3) with (M+(M+3)) at 1 by math.
      rewrite <- ! hstar_interval_offset.
      subst pall vall. simpl.
      case_if; try math.

      apply himpl_frame_lr.
      1:{ unfold pind, vind.
        case_if; try math. 
        replace (abs 0)%nat with 0%nat by math.
        by rewrite Nat.add_0_r.
      }
      apply himpl_frame_lr.
      1:{ unfold pind, vind.
        apply hbig_fset_himpl.
        intros. rewrite indom_interval in H0. repeat case_if; try math.
        replace (px_ind + 1 + abs d0)%nat with (px_ind + abs (d0 + 1))%nat by math.
        replace (d0+1-1) with d0 by math. by [].
      }
      apply himpl_frame_lr.
      1:{ unfold pval, vval.
        rewrite intervalU. 2: math.
        rewrite hbig_fset_update. 3-4: auto. 2: rewrite indom_interval; intros ?; math.
        rewrite intervalgt. 2: math.
        rewrite hbig_fset_empty.
        repeat case_if; try math.
        replace (abs (0 + (M + 2) - (M + 2)))%nat with 0%nat by math.
        rewrite Nat.add_0_r. xsimpl.
      }
      1:{ unfold pval, vval.
        apply hbig_fset_himpl.
        intros. rewrite indom_interval in H0. repeat case_if; try math.
        replace (abs (d0 + (M + 3) - (M + 2)))%nat with (1+abs d0)%nat by math.
        replace (px_val + 1 + abs d0)%nat with (px_val + (1 + abs d0))%nat by math.
        replace (d0 + (M + 3) - (M + 2) - 1) with d0 by math.
        by [].
      }
    }
    {
      match goal with |- himpl (hsub ?a _) (hsub ?b _) => enough (a = b) as Hg end.
      1: by rewrite Hg.

      rewrite -> intervalU with (x:=0) (y:=M+M+3).
      2: math.
      rewrite hbig_fset_update; try assumption.
      3-4: auto.
      2: rewrite indom_interval; intros ?; math.
      rewrite <- interval_union with (x:=0+1) (z:=M+M+3) (y:=M+2); try math.
      rewrite hbig_fset_union; try assumption.
      2-4: hnf; auto.
      2:{
        apply disjoint_of_not_indom_both.
        intros ?. rewrite ! indom_interval. intros; math.
      }
      rewrite <- interval_union with (x:=M+2) (z:=M+M+3) (y:=M+3); try math.
      rewrite hbig_fset_union; try assumption.
      2-4: hnf; auto.
      2:{
        apply disjoint_of_not_indom_both.
        intros ?. rewrite ! indom_interval. intros; math.
      }
      replace (M+2) with ((M+1)+1) at 1 by math.
      replace (M+2) with (0+(M+2)) by math.
      replace (M+3) with (1+(M+2)) at 1 by math.
      replace (M+3) with (0+(M+3)) at 1 by math.
      replace (M+M+3) with (M+(M+3)) at 1 by math.
      rewrite <- ! hstar_interval_offset.
      subst pall vall. simpl.
      case_if; try math.

      f_equal.
      1:{ unfold pind, vind.
        case_if; try math. 
        replace (abs 0)%nat with 0%nat by math.
        by rewrite Nat.add_0_r.
      }
      f_equal.
      1:{ unfold pind, vind.
        rewrite <- hbig_fset_hstar.
        apply hbig_fset_eq.
        intros. rewrite indom_interval in H0. repeat case_if; try math.
        replace (px_ind + 1 + abs d0)%nat with (px_ind + abs (d0 + 1))%nat by math.
        replace (d0+1-1) with d0 by math. by [].
      }
      f_equal.
      1:{ unfold pval, vval.
        rewrite intervalU. 2: math.
        rewrite hbig_fset_update. 3-4: auto. 2: rewrite indom_interval; intros ?; math.
        rewrite intervalgt. 2: math.
        rewrite hbig_fset_empty.
        repeat case_if; try math.
        replace (abs (0 + (M + 2) - (M + 2)))%nat with 0%nat by math.
        rewrite Nat.add_0_r. xsimpl.
      }
      1:{ unfold pval, vval.
        rewrite <- hbig_fset_hstar.
        apply hbig_fset_eq.
        intros. rewrite indom_interval in H0. repeat case_if; try math.
        replace (abs (d0 + (M + 3) - (M + 2)))%nat with (1+abs d0)%nat by math.
        replace (px_val + 1 + abs d0)%nat with (px_val + (1 + abs d0))%nat by math.
        replace (d0 + (M + 3) - (M + 2) - 1) with d0 by math.
        by [].
      }
    }
  }
  (* post sub *)
  { 
    (* into a better shape *)
    (* moving the \Top to innermost still does not work! *)
    apply qimpl_trans with (Q2:=fun hv =>
      hsub
        (\[(hv \o f) (⟨(1, 0), 0⟩)%arr =
          fset_fold (val_int 0) (fun d acc => val_int_add acc (hv (f d)))
            (label (Lab (pair 2 0) (interval 0 N)))] \* 
        (@hexists loc (fun px => \[((hv \o f) (Lab (pair 3 0) 0)) = val_loc px] \*
            (@hexists (list val) (fun Larr =>
            \[length Larr = (abs N)] \* 
            (\*_(d <- ⟨pair 4 0, interval 0 N⟩) \[(hv \o f) d = (nth (abs (eld d)) Larr)]) \*
            harray Larr px (Lab (pair 3 0) 0))))) \*
        (\*_(d <- ⟨(1, 0), single 0 tt⟩)
          arr_x_ind px_ind d \* arr_x_val px_val d) \*
        (\*_(d <- ⟨(3, 0), single 0 tt⟩)
          arr_x_ind px_ind d \* arr_x_val px_val d) \*
        (\*_(d <- ⟨(2, 0), interval 0 N⟩)
          arr_x_ind px_ind d \* arr_x_val px_val d) \*
        (\*_(d <- ⟨(4, 0), interval 0 N⟩)
          arr_x_ind px_ind d \* arr_x_val px_val d)) f).
    1:{
      xsimpl. intros.
      match goal with |- himpl (hsub ?a _) (hsub ?b _) => 
        assert (a = b) as HHH end.
      1:{
        (* hand control *)
        rewrite hstar_assoc.
        f_equal.
        rewrite -> hstar_comm.
        rewrite -> hstar_assoc.
        f_equal.
        xsimpl.
      }
      by rewrite HHH.
    }
    hnf. intros v.
    rewrite -> hsub_hpure_comm. apply himpl_hstar_hpure_l.
    intros H1.
    rewrite -> hstar_hexists_comm.
    rewrite -> hsub_hstar. apply himpl_hexists_l.
    intros px.
    rewrite hstar_assoc.
    rewrite -> hsub_hpure_comm. apply himpl_hstar_hpure_l.
    intros H2.
    rewrite -> hstar_hexists_comm.
    rewrite -> hsub_hstar. apply himpl_hexists_l.
    intros Larr.
    rewrite hstar_assoc.
    rewrite -> hsub_hpure_comm. apply himpl_hstar_hpure_l.
    intros H3.
    rewrite hstar_assoc.
    rewrite -> hstar_fset_pure.
    rewrite -> hsub_hpure_comm. apply himpl_hstar_hpure_l.
    intros H4.
    rewrite -> hsub_hstar_id_l with (fs:=⟨(3, 0), single 0 tt⟩).
    1: apply himpl_frame_lr. 
    2:{
      hnf. intros h Hh. apply hhtop_intro'. 
      hnf in Hh. destruct Hh as (h' & <- & Hvsub & Hh').
      apply fsubst_indom_local.
      intros. rewrite fsubst_valid_indom in H.
      destruct H as ((p', d') & Epd & H).
      simpl in Epd. inversion Epd. subst p d.

      match type of Hh' with ?HHH _ => assert (hlocal HHH 
        (⟨(1, 0), single 0 tt⟩ \u ⟨(2, 0), interval 0 N⟩ \u ⟨(3, 0), single 0 tt⟩ \u ⟨(4, 0), interval 0 N⟩))
       as Htmp end.
      {
        hlocal.
        1: apply hlocal_union_l.
        2: apply hlocal_union_r, hlocal_union_r, hlocal_union_l.
        3: apply hlocal_union_r, hlocal_union_l.
        4: apply hlocal_union_r, hlocal_union_r, hlocal_union_r.
        all: apply hlocal_hstar_fset.
        1-2: intros d; rewrite label_single indom_single_eq; intros <-.
        1-2: hlocal; apply hlocal_harray.
        all: intros (l', d''); rewrite indom_label_eq; intros (<- & Hin).
        1: apply hlocal_subset with (fs1:=single (Lab (2, 0) d'') tt).
        3: apply hlocal_subset with (fs1:=single (Lab (4, 0) d'') tt).
        1,3: intros (?, ?); rewrite indom_single_eq; intros <-; 
          by rewrite indom_label_eq.
        all: hlocal; apply hlocal_harray.
      }
      apply Htmp in Hh'. clear Htmp.
      apply Hh' in H.
      destruct d' as (l', d').
      rewrite ! indom_union_eq ! indom_label_eq ! indom_single_eq in H.
      subst f. simpl. 
      rewrite ! indom_union_eq ! indom_label_eq ! label_single ! indom_single_eq.
      repeat case_if; simpl; rewrite indom_label_eq; try eqsolve.
      intuition; try subst; eqsolve.
    }
    4:{ rewrite label_single. apply hlocal_harray. }
    2:{
      intros (ll, d). rewrite label_single indom_single_eq. intros <-.
      subst f. simpl. rewrite indom_label_eq. case_if; eqsolve.
    }
    2:{
      subst f. simpl.
      intros (ll, d) (ll', d') H HH.
      rewrite ! indom_label_eq in HH.
      rewrite ! label_single ! indom_single_eq. 
      repeat case_if; try eqsolve.
    }
    apply himpl_hexists_r with (x:=px).
    assert (f[1](0) = (Lab (1, 0) 0)) as Hid1.
    { subst f. simpl. rewrite indom_label_eq. case_if; eqsolve. }
    assert (f[3](0) = (Lab (3, 0) 0)) as Hid3.
    { subst f. simpl. rewrite indom_label_eq. case_if; eqsolve. }
    assert (forall d, indom (interval 0 N) d -> f[2](d) = (Lab (2, 0) d)) as Hid2.
    { subst f. simpl. intros. rewrite indom_label_eq. case_if; eqsolve. }
    assert (forall d, indom (interval 0 N) d -> f[4](d) = (Lab (2, 0) d)) as Hid4.
    { subst f. simpl. intros. rewrite indom_label_eq. case_if; eqsolve. }
    assert (forall d : int, indom (interval 0 N) d -> v[2](d) = nth (abs d) Larr) as Htmp.
    { intros. rewrite <- Hid4; auto. apply H4. by rewrite indom_label_eq. }
    simpl in H2. rewrite Hid3 in H2.
    apply himpl_hstar_hpure_r; auto.
    apply himpl_hexists_r with (x:=Larr).
    simpl in H1. rewrite Hid1 in H1.
    apply himpl_hstar_hpure_r; auto.
    1:{ split; auto. rewrite H1.
      rewrite -> fold_fset_eq with (f2:=fun d acc => val_int (val_int_add acc (v d))).
      2:{ intros (l, d). rewrite indom_label_eq. intros (<- & H). 
        extens. intros. rewrite Hid2; auto.
      }
      simpl in H4.
      rewrite -> fold_fset_summation_dedicated with (Larr:=Larr); try math; auto.
      apply zero_le_N.
    }
    (* xsimpl. rewrite hstar_fset_pure. xsimpl. auto. *)
  }
Qed.

(* final theorem *)
Theorem rlsum_rl_ntriple : forall (px_ind px_val : loc),
  ntriple 
    ((\*_(d <- ⟨pair 1 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
      (\*_(d <- ⟨pair 3 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))))
    ((Lab (pair 1 0) (FH (single 0 tt) (fun=> (rlsum_func M px_ind px_val)))) :: 
      (Lab (pair 3 0) (FH (single 0 tt) (fun=> (rl_func N px_ind px_val)))) :: 
      nil)
    (fun hv => 
      (@hexists loc (fun px => \[(hv (Lab (pair 3 0) 0)) = val_loc px] \*
        (@hexists (list val) (fun Larr =>
        \[length Larr = (abs N) /\
        hv (Lab (pair 1 0) 0) = fold_left val_int_add (val_int 0) Larr] \* 
        harray Larr px (Lab (pair 3 0) 0))))) \* \Top).
Proof.
  intros.
  unfold ntriple, nwp.
  remember ((Lab (pair 1 0) (FH (single 0 tt) (fun=> (rlsum_func M px_ind px_val)))) :: 
    (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
    (Lab (pair 3 0) (FH (single 0 tt) (fun=> (rl_func N px_ind px_val)))) :: 
    nil) as lsq eqn:E.
  simpl fset_of. rew_fmap.
  rewrite -> wp_ht_eq with (ht2:=htrm_of lsq).
  2:{
    intros (ll, d) HH. rewrite indom_union_eq ! indom_label_eq ! indom_single_eq in HH.
    subst lsq. unfold htrm_of. simpl.
    rewrite ! indom_single_eq. repeat case_if; try eqsolve.
  }
  assert (fset_of lsq = (⟨(1, 0), single 0 tt⟩ \u ⟨(3, 0), single 0 tt⟩ \u ⟨(2, 0), interval 0 N⟩)) as Efs.
  { subst lsq. unfold fset_of. simpl. rew_fmap. 
    rewrite -> union_comm_of_disjoint with (h1:=⟨(2, 0), interval 0 N⟩). 1: reflexivity.
    apply disjoint_of_not_indom_both. intros (ll, d). rewrite ! indom_label_eq ! indom_single_eq.
    intros. eqsolve.
  }
  apply wp_equiv.
  eapply htriple_conseq.
  1:{
    pose proof (rlsum_rl_rli_ntriple px_ind px_val) as H.
    unfold ntriple, nwp in H. rewrite wp_equiv in H.
    rewrite <- ! E in H.
    rewrite hstars_pick_last_3 in H.
    rewrite <- hstar_assoc in H.
    rewrite -> hstar_comm with (H1:=(\*_(d <- ⟨(3, 0), single 0 tt⟩)
      arr_x_ind px_ind d \* arr_x_val px_val d)) in H.
    rewrite -> ! hhtop_hstar in H.
    eapply htriple_proj' with (fs':=⟨(2, 0), interval 0 N⟩)
      (Q':=fun=> \[Top ⟨(2, 0), interval 0 N⟩]).
    7:{
      rewrite union_assoc.
      match goal with |- htriple ?fs _ _ _ => replace fs with (fset_of lsq) end.
      (* rewrite <- Efs. *)
      eapply htriple_conseq.
      1: apply H. 1: apply himpl_refl.
      hnf. intros v. 
      rewrite -> hstar_comm with (H1:=hhtop ⟨(2, 0), interval 0 N⟩).
      rewrite -> hstars_pick_last_4.
      rewrite -> hstar_comm with (H2:=hhtop ⟨(2, 0), interval 0 N⟩).
      apply himpl_refl.
    }
    1:{
      rew_disjoint. split.
      all: apply disjoint_of_not_indom_both; intros (?, ?).
      all: rewrite ! indom_label_eq ! indom_single_eq; eqsolve.
    }
    1:{
      hlocal.
      1: apply hlocal_union_l.
      2: apply hlocal_union_r.
      all: apply hlocal_hstar_fset.
      1-2: intros d; rewrite label_single indom_single_eq; intros <-.
      1-2: hlocal; apply hlocal_harray.
    }
    2:{
      apply hlocal_hstar_fset.
      intros (ll, d). rewrite indom_label_eq. intros (<- & HH).
      apply hlocal_subset with (fs1:=single (Lab (2, 0) d) tt).
      1: intros (?, ?); rewrite indom_single_eq; intros <-; 
        by rewrite indom_label_eq.
      hlocal; apply hlocal_harray.
    }
    3:{
      (* show that the array is replicatable *)
      intros. apply hstar_inv in H0.
      destruct H0 as (h1 & _ & Hh1 & _).
      rewrite hstar_fsetE in Hh1.
      destruct Hh1 as (hi & -> & Ha & Hb).
      setoid_rewrite label_single in Hb.
      specialize (Hb _ (indom_single _ _)).
      apply hstar_inv in Hb.
      destruct Hb as (h1 & h2 & Hh1 & Hh2 & Hdj & EE).
      apply harray_inv in Hh1, Hh2.
      unfold null in Hh1, Hh2.
      destruct Hh1 as (Eh1 & Hn1), Hh2 as (Eh2 & Hn2).
      assert (px_ind <> 0%nat) as Hn1' by (intros ->; by apply Hn1).
      assert (px_val <> 0%nat) as Hn2' by (intros ->; by apply Hn2).
      clear Hn1 Hn2.
      eexists. rewrite hstar_fsetE.
      exists (fun (li : D) => 
        (hconseq (val_header (abs (M+1)) :: (LibList.map val_int Lind)) px_ind li) \u
        (hconseq (val_header (abs M) :: (LibList.map val_int Lval)) px_val li)).
      split. 1: reflexivity.
      split.
      {
        intros. rew_disjoint.
        repeat split.
        all: apply hconseq_disjoint_suffcond1; eqsolve.
      }
      {
        intros (ll, d). rewrite indom_label_eq. intros (<- & Hin).
        apply hstar_intro.
        1-2: apply harray_intro.
        1,3: by rewrite length_map.
        1-2: intros Htmp; inversion Htmp; eqsolve.
        subst h1 h2.
        rewrite ! length_map in Hdj.
        rewrite H_length_Lind H_length_Lval in Hdj.
        eapply hconseq_disjoint_nececond1.
        1: apply Hdj.
        eqsolve.
      }
    }
    2:{ intros _. apply hhtop_hlocal. }
    {
      intros. simpl. hlocal.
      2: apply hlocal_union_l, hhtop_hlocal.
      2: apply hlocal_union_r, hhtop_hlocal.
      apply hlocal_union_r. rewrite label_single. apply hlocal_harray.
    }
  }
  1: xsimpl.
  hnf. intros v.
  apply himpl_frame_lr. 2: xsimpl.
  apply himpl_refl.
Qed.

End MainProof.

End Demo.
