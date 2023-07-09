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

(* Module ArrayDemo (Dom : Domain). *)

Module Export AD := WithArray(IntDom).
Check eq_refl : D = labeled int.

Global Instance Inhab_D : Inhab D. 
Proof Build_Inhab (ex_intro (fun=> True) (Lab (0, 0) 0) I).

Section Demo.

(* another version of xfor_lemma *)

Definition Sum (fs : fset int) (f : int -> int) : int :=
  fset_fold 0 (fun idx acc => acc + (f idx)) fs.
Reserved Notation "'Σ_' ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' Σ_ ( i  <-  r ) '/  '  F ']'").

Notation "'Σ_' ( i <- r ) F" :=
  (Sum r (fun i => F)) : nat_scope.

Lemma Sum0 : Sum empty = fun=> 0.
Proof. unfold Sum. extens. intros F. rewrite -> (fst (@fset_foldE _ _ _ _)); auto. Qed.

Lemma SumxSx l : Sum (interval l (l + 1)) = @^~ l.
Proof. 
  extens. intros f.
  unfold Sum. rewrite -> intervalUr. 2: math.
  rewrite -> (snd (@fset_foldE _ _ _ _)); auto.
  2: math.
  2: rewrite -> intervalgt. 2: unfolds indom, map_indom; simpl; eqsolve.
  2: math.
  rewrite -> intervalgt. 2: math.
  rewrite -> (fst (@fset_foldE _ _ _ _)); auto.
Qed.

Lemma SumPart x y z F : x <= y <= z -> 
  Sum (interval x z) F = Sum (interval x y) F + Sum (interval y z) F.
Proof.
  remember (abs (z - y)) as n.
  revert y z Heqn. induction n; intros.
  { assert (z = y) as -> by math.
    rewrite -> intervalgt with (x:=y) (y:=y).
    2: math.
    rewrite -> Sum0. math.
  }
  { assert (z = (y + (nat_to_Z n)) + 1) as -> by math.
    rewrite -> intervalUr.
    2: math.
    rewrite -> intervalUr.
    2: math.
    unfold Sum at 1. unfold Sum at 2.
    rewrite -> ! (snd (@fset_foldE _ _ _ _)); try math.
    { fold (Sum (interval x (y + n)) F).
      fold (Sum (interval y (y + n)) F).
      rewrite -> IHn with (y:=y); try math.
    }
    { rewrite -> indom_interval. intros HH. math. }
    { rewrite -> indom_interval. intros HH. math. }
  }
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

Lemma wp_for_aux_alt i fs fs' ht (H : int -> int -> int -> (D -> val) -> hhprop) Z N C fsi hv0 k vr:
  (Z <= i <= N)%Z ->
  (* (forall x y z hv1 hv2, x <= y <= z -> H x y hv1 \* H y z hv2 ==> \exists hv, H x z hv) -> *)
  (* (forall k Z i hv, exists k', forall j, H k' i j hv = H k Z j hv) -> *)
  (forall i j k hv1 hv2, (forall x, indom (Union (interval i j) fsi) x -> hv1 x = hv2 x) -> H k i j hv1 = H k i j hv2) ->
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  fs = Union (interval i N) fsi ->
  (forall t, subst "for" t C = C) ->
  (forall t, subst "cnt" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  disjoint fs' fs ->
  (forall x, indom fs' x -> ht x = For i N (trm_fun vr C)) ->
  (forall j k hv, (Z <= j < N)%Z -> H k Z j hv ==> 
    wp
      (fs' \u fsi j) 
      ((fun=> subst vr j C) \u_fs' ht) 
      (fun hr => H k Z (j + 1) (hv \u_(Union (interval Z j) fsi) hr))) ->
  H k Z i hv0 ==> 
    wp
      (fs' \u fs)
      ht 
      (fun hr => H k Z N (hv0 \u_(Union (interval Z i) fsi) hr)).
Proof. 
  move=> + hP Dj -> sfor scnt scond vcnt vfor vcond  + +.
  move: ht hv0.
  induction_wf IH: (upto N) i; rewrite /upto le_zarith lt_zarith in IH.
  move=> ht hv0 lN dj htE.
  rewrite -wp_union // (wp_ht_eq _ _ _ htE) /For /For_aux.
  rewrite wp_fix_app2.
  Opaque subst.
  xwp.
  Transparent subst. 
  rewrite vcnt vfor sfor /=.
  xapp; rewrite vcond scnt scond.
  xwp; xif; rewrite lt_zarith.
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
    rewrite (wp_union (fun hr2 => H k Z N (_ \u_ _ hr2))) //.
    rewrite // intervalU. 2: math.
    rewrite // Union_upd // -union_assoc.
    rewrite union_comm_of_disjoint -?union_assoc; first rewrite union_comm_of_disjoint.
    2-3: move: dj; rewrite disjoint_union_eq_l ?disjoint_Union.
    2-3: setoid_rewrite indom_interval=> dj; do ?split.
    2-5: by intros; (apply/dj; math) + (apply/Dj; math).
    rewrite -wp_union; first last.
    { move: dj; rewrite disjoint_union_eq_r ?disjoint_Union.
      setoid_rewrite indom_interval=> dj; split=> *; [apply/Dj|apply/dj]; math. }
    set (ht' := (fun=> subst vr i C) \u_fs' ht).
    rewrite (wp_ht_eq _ ht'); first last.
    { by move=> *; rewrite subE /ht' uni_in. }
    rewrite (wp_ht_eq (_ \u_ _ _) ht'); first last.
    { move=> ??; rewrite /ht' ?uni_nin // => /(@disjoint_inv_not_indom_both _ _ _ _ _); apply; eauto.
      all: rewrite indom_Union; setoid_rewrite indom_interval; do? eexists;eauto; math. }
    apply: himpl_trans; last apply/wp_union2; first last.
    { move: dj; rewrite disjoint_Union disjoint_comm; apply.
      rewrite indom_interval; math. }
    have: (Z <= i < N)%Z by math.
    move: (H0 i k hv0)=> /[apply]/wp_equiv S; xapp S.
    move=> hr.
    apply: himpl_trans; first last.
    { apply: wp_conseq=> ?; rewrite uniA=> ?; exact. }
    set (hv0 \u_ _ _); rewrite [_ \u fsi i]union_comm_of_disjoint; first last.
    { rewrite disjoint_Union.
      setoid_rewrite indom_interval=> *; apply/Dj; math. }
    rewrite -Union_upd // -intervalUr; last math.
    rewrite union_comm_of_disjoint; first last.
    { move: dj; rewrite ?disjoint_Union; setoid_rewrite indom_interval.
      move=> dj *; apply/dj; math. }
    apply IH; try math.
    { move: dj; rewrite ?disjoint_Union; setoid_rewrite indom_interval.
      move=> dj *; apply/dj; math. }
    { by move=> *; rewrite uni_in. }
    move=> j ??.
    rewrite (wp_ht_eq _ ((fun=> (subst vr j C)) \u_ fs' ht)); eauto.
    move=> ??; rewrite /uni. case: classicT=> //. }
    move=> ?; have->: i = N by math.
    xwp; xval.
    rewrite intervalgt ?Union0; last math.
    rewrite wp0_dep. xsimpl hv0.
    erewrite hP; eauto.
    by move=> ??; rewrite uni_in. 
Qed.

Lemma wp_for_alt fs fs' ht (H : int -> int -> int -> (D -> val) -> hhprop) Z N (C : trm) fsi hv0 k (P : hhprop) Q vr :
(* (forall x y z hv1 hv2, x <= y <= z -> H x y hv1 \* H y z hv2 ==> \exists hv, H x z hv) -> *)
  (forall k i hv, exists k', 
    forall j hv', (Z <= i <= j)%Z -> (forall x, indom (Union (interval Z i) fsi) x -> hv x = hv' x) -> 
      H k' i j hv' = H k Z j hv') ->
  (forall j k hv, (Z <= j < N)%Z -> H k j j hv ==> wp (fs' \u fsi j) ((fun=> subst vr j C) \u_fs' ht) (H k j (j + 1))) ->
  (forall i j k hv1 hv2, (forall x, indom (Union (interval i j) fsi) x -> hv1 x = hv2 x) -> H k i j hv1 = H k i j hv2) ->
  (P ==> H k Z Z hv0) -> 
  (H k Z N ===> Q) ->
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  (Z <= N)%Z ->
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
  move=> hp Hwp Heq HP HQ Dj *.
  apply: himpl_trans; first exact/HP.
  apply: himpl_trans; first last.
  { apply: wp_conseq; exact/HQ. }
  apply: himpl_trans.
  { apply/(@wp_for_aux_alt Z); eauto; first math.
    clear -hp Hwp Heq Dj=> i k hv lP.
    case: (hp k i hv)=> k' /[dup]HE<- //; last math.
    move=> ? // /Hwp-/(_ lP). apply/wp_conseq=> hr.
    rewrite -(HE _ (hv \u_ (Union (interval Z i) fsi) hr)).
    { erewrite Heq; eauto=> ? IND; rewrite uni_nin //.
      move: IND; rewrite ?indom_Union.
      do ? setoid_rewrite indom_interval.
      case=> ? [?] /[swap]-[?][?].
      apply/disjoint_inv_not_indom_both/Dj; math. }
    { math. }
    by move=> ??; rewrite uni_in. }
  apply/wp_conseq=> ?; rewrite intervalgt ?Union0 ?uni0 //; by math.
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
  eapply wp_for_alt with 
    (H:=(fun x (r : int) q hv => 
      Inv q \* 
      (\*_(d <- Union (interval Z q) fsi1) R' d) \*
      (\*_(d <- Union (interval q N) fsi1) R d) \* 
      p ~⟨(i, 0%Z), s⟩~> (x + Σ_(l <- interval r q) op hv l)))
    (hv0:=fun=> 0) (k:=0)=> //; try eassumption.
  { move=> k r hv.
    exists (k + Σ_(l <- interval Z r) op hv l)=> t hv' lP hvE.
    suff->: 
      k + Σ_(l <- interval Z r) op hv l +
      Σ_(l <- interval r t) op hv' l = 
      k + Σ_(l <- interval Z t) op hv' l by xsimpl.
    rewrite (SumPart _ lP).
    suff->: 
      Σ_(l <- interval Z r) op hv' l = 
      Σ_(l <- interval Z r) op hv l by math.
    apply/SumEq=> *. 
    apply/eq_sym/opP=> *; apply/hvE.
    rewrite indom_Union; eexists; rewrite indom_label_eq; eauto. }
  { clear -IH Dj iNj.
    move=>l x hv ?; move: (IH l x).
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil SumxSx.
    rewrite union_empty_r [interval l l]intervalgt; last math.
    rewrite Sum0 Z.add_0_r intervalUr; try math.
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
    erewrite wp_ht_eq.
    { apply: xapp_lemma'; [|rewrite <-wp_equiv; apply/Hwp; math|].
      { reflexivity. }
      unfold protect.
      rew_heap.
      xsimpl*.
      move: (hbig_fset hstar (fsi1 _) _)=> HR.
      rewrite -hstar_assoc [_ \* HR]hstar_comm hstar_assoc.
      xsimpl. }
    case=> l' ?; rewrite indom_union_eq ?indom_label_eq=> -[][??]; subst.
    { rewrite uni_in ?indom_label_eq //= /htrm_of.
      case: classicT=> //; autos*. }
    rewrite uni_nin ?indom_label_eq /= /htrm_of; autos*.
    2: eqsolve.
    do ? (case: classicT; autos* ).
    1: simpl; eqsolve.
    move=> [_]?[]; split=> //.
    rewrite indom_Union; setoid_rewrite indom_interval; do ? (eexists; eauto); try math. }
  { move=> q r k hv hv' hvE.
    suff->:
      Σ_(l <- interval q r) op hv l = 
      Σ_(l <- interval q r) op hv' l by xsimpl.
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

(* assume properties about the running-length encoding. *)
(*
Variables (N M : nat) (Lval : list int) (Lind : list nat).
Hypothesis H_length_Lval : length Lval = M.
Hypothesis H_length_Lind : length Lind = S M.
Hypothesis H_Lind_first : nth 0%nat Lind = 0%nat.
Hypothesis H_Lind_last : nth M Lind = N.
Hypothesis H_Lind_inc : forall (i j : nat), 0%nat <= i < M -> 0%nat <= j <= M -> 
  (i < j)%nat -> nth i Lind < nth j Lind.
Hypothesis H_Lval_notnil : (1 <= M)%nat.
*)

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

  (* trm_fun "i"
  (val_set real_s
     (val_get
        (val_add real_s
           (val_mul (val_array_get real_x_val "i")
              (val_sub (val_array_get real_x_ind (val_add "i" 1))
                 (val_array_get real_x_ind "i")))))). *)

Definition rlsum_func :=
  let loopbody := rlsum_loopbody "x_ind" "x_val" "s" "i" in
  let loop := For 0 M (trm_fun "i" loopbody) in
  (* the arguments should be the location of arrays? *)
  <{ fun "x_ind" "x_val" => 
      let "s" = ref 0 in 
      loop ; 
      ! "s"
  }>.

Definition rli_whilecond (i : int) (real_x_ind real_j : trm) :=
  (* intermediate lang *)
  (* (<{ (val_array_get real_x_ind (! (real_j + 1))) <= i }>). *)
  (<{ let "tmp1" = ! real_j in
      let "tmp2" = "tmp1" + 1 in
      let "tmp3" = val_array_get real_x_ind "tmp2" in
      "tmp3" <= i }>).

Definition rli_whilebody (real_j : trm) :=
  (* or incr j? *)
  (* (<{ real_j := (! real_j) + 1 }>). *)
  (<{ let "tmp1" = ! real_j in
      let "tmp2" = "tmp1" + 1 in
      real_j := "tmp2" }>).

Definition rli_func (i : int) :=
  let loop := While (rli_whilecond i "x_ind" "j")
    (rli_whilebody "j") in
  <{ fun "x_ind" "x_val" => 
      let "j" = ref 0 in 
      loop ; 
      (let "tmp" = ! "j" in (val_array_get "x_val" "tmp"))
  }>.

Definition arr_x_ind (p : loc) (d : D) :=
  (* harray (LibList.map (fun n => val_int (Z.of_nat n)) Lind) p d. *)
  harray (LibList.map val_int Lind) p d.

Definition arr_x_val (p : loc) (d : D) :=
  harray (LibList.map val_int Lval) p d.

(* sums are equal *)

Fact For_subst ZZ NN t x v : 
  x <> "cond" -> 
  x <> "for" ->
  x <> "cnt" -> 
  x <> "body" ->
  subst x v (For ZZ NN t) = For ZZ NN (subst x v t).
Proof using.
  intros. unfold For, For_aux. simpl; case_var; eqsolve.
Qed.

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

(* Definition int_add_val_int (b : int) (a : val) :=
  b + (match a with val_int a' => a' | _ => 0 end). *)

(*
(* a subgoal for goal and other programs *)
Goal forall (px_ind px_val : loc) (ps0 : loc),
  ntriple 
    (ps0 ~⟨(1%Z, 0%Z), 0⟩~> 0 \*
      arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
      arr_x_val px_val (⟨(1, 0), 0⟩)%arr \*
      (\*_(d <- interval 0 N)
          arr_x_ind px_ind (⟨(2, 0), d⟩)%arr \*
          arr_x_val px_val (⟨(2, 0), d⟩)%arr))
    ((Lab (pair 1 0) (FH (single 0 tt) (fun=> 
      For 0 M (rlsum_loopbody (val_loc px_ind) (val_loc px_val) (val_loc ps0))
      ))) :: 
      (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => (fun hveta => ps0 ~⟨(1%Z, 0%Z), 0⟩~> 
      (fset_fold 0 (fun d acc => int_add_val_int acc (hveta d)) 
        (label (Lab (pair 2 0) (interval 0 N)))) \* \Top) hv).
Proof.
  intros.
  unfold rlsum_loopbody.
  eapply xfor_lemma.




*)

Definition ind_seg (i : int) := 
  (* interval (Z.of_nat (nth (Z.to_nat i) Lind)) (Z.of_nat (nth (Z.to_nat (i + 1)) Lind)). *)
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
    (* TODO may reuse disjoint proof *)
    apply disjoint_of_not_indom_both.
    intros. rewrite -> indom_interval in *. math.
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

(* order property of this array *)
(* Lemma ind_find_unique : forall (k : int)
  (Hk : (0 <= k < N)%Z) (a : int) (Ha : (0 <= a < M)%Z) 
  (Hka : (nth (abs a) Lind <= k < nth (abs (a + 1)) Lind)%Z),  *)

(*
Lemma interval_segmentation_pre i :
  0 <= i <= M -> 
  Union (interval 0 i) ind_seg = interval 0 (Z.of_nat (nth (Z.to_nat i) Lind)).
Proof using N M Lind H_length_Lind H_Lind_first H_Lind_inc.
  clear Lval H_length_Lval H_Lind_last H_Lval_notnil.

  remember (to_nat i) as n.
  revert i Heqn.
  induction n as [ | n IH ]; intros.
  { assert (i = 0) as -> by math. 
    rewrite -> H_Lind_first. simpl. rewrite -> intervalgt; try math.
    by rewrite -> Union0.
  }
  { assert (i = (Z.of_nat n) + 1) as -> by math.
    rewrite -> intervalUr; try math.
    rewrite -> Union_upd_fset, -> IH; try math.
    unfold ind_seg. 
    replace (to_nat (Z.of_nat n)) with n by math.
    replace (to_nat (Z.of_nat n + 1)) with (S n) by math.
    rewrite <- interval_union with (x:=0) (y:=(Z.of_nat (nth n Lind)))
      (z:=(Z.of_nat (nth (S n) Lind))); try math.
    2:{ apply inj_le, H_Lind_inc; math. }
    rewrite -> union_comm_of_disjoint. 1: reflexivity.
    (* TODO may reuse disjoint proof *)
    apply disjoint_of_not_indom_both.
    intros. rewrite -> indom_interval in *. math.
  }
Qed.

Lemma interval_segmentation :
  Union (interval 0 M) ind_seg = interval 0 N.
Proof using N M Lind H_length_Lind H_Lind_first H_Lind_inc H_Lind_last.
  clear Lval H_length_Lval H_Lval_notnil.

  rewrite -> interval_segmentation_pre with (i:=M). 2: math.
  rewrite <- H_Lind_last.
  f_equal. replace (to_nat M) with M by math. math.
Qed.
*)

Fact UnionN0 [T D S : Type] (fs : fset T) : Union fs (fun=> @empty D S) = empty.
Proof using.
  pattern fs. apply fset_ind; clear fs.
  { by rewrite -> Union0. }
  { intros. rewrite -> Union_upd. 2: auto. by rewrite -> H, -> union_empty_l. }
Qed.

Lemma hbig_fset_label_single' (Q : D -> hhprop) (d : D) :
  \*_(d0 <- single d tt) Q d0 = Q d.
Proof using.
  unfold hbig_fset.
  rewrite -> update_empty. rewrite -> (snd (@fset_foldE _ _ _ _)); auto.
  2: intros; xsimpl.
  rewrite -> (fst (@fset_foldE _ _ _ _)); auto.
  by rewrite -> hstar_hempty_r.
Qed.

(* sub-part: evaluating while condition *)
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
    (fun hv => \[hv d = val_int (nth (abs a) Lval)] \* arr_x_ind px_ind d \* arr_x_val px_val d \* \Top).
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
      (trm_let "tmp" (val_get pj0) (val_array_get px_val "tmp"))).
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
(*
Lemma htriple_hmerge_frame fs ht P Q p d (v diff : int) : 
  (forall (v diff : int), 
    htriple fs ht (hsingle p d v) 
      (fun=> hstar (hsingle p d (v + diff)) (hpure P))) ->
  htriple fs ht 
    (hmerge val_int_add Q (hsingle p d v))
    (fun=> hstar (hmerge val_int_add Q (hsingle p d (v + diff))) (hpure P)).
Proof.
  intros H.
  unfold htriple in H |- *. intros H'.
  unfold hhoare in H |- *. intros h Hh.
  unfold hmerge in Hh. apply hstar_inv in Hh.
  destruct Hh as (hm & hh' & (hq & hs & Hq & Hs & Em) & Hh' & Hdj & E).
  apply hsingle_inv in Hs.
  subst h hs. 

  destruct (fmap_data hm (p, d)) eqn:E.
  2:{ 
    subst hm. unfold Fmap.merge, Fmap.map_merge in E. simpl in E.
    case_if.
    by destruct (fmap_data hq (p, d)) eqn:E'.
  }
  assert (exists delta, v0 = val_int (v + delta)).
  {
    subst hm. unfold Fmap.merge, Fmap.map_merge in E. simpl in E.
    case_if.
    destruct (fmap_data hq (p, d)) eqn:E'.
    { destruct (match v1 with val_int _ => true | _ => false end) eqn:E2.
      { destruct v1; try eqsolve.
        unfold val_int_add in E. injection E as <-.
        exists z. math.
      }
      { destruct v1; try eqsolve.
        all: unfold val_int_add in E; injection E as <-.
        all: exists 0; math.
      }
    }
    injection E as <-.
    exists 0; math.
  }
  destruct H0 as (delta & ->).
  
  specialize (H (v + delta) diff H'
    (Fmap.union (Fmap.single (p, d) (val_int (v + delta))) hh')).
  match type of H with ?a -> _ => assert a as Hhead end.
  { apply hstar_intro; try assumption.
    1: apply hsingle_intro.
    apply disjoint_of_not_indom_both.
    intros. 
    assert (indom hm x) as Htmp.
    { subst hm. rewrite -> indom_merge_eq. right.
      by rewrite -> indom_single_eq in H0 |- *.
    }
    revert Htmp H1. by apply disjoint_inv_not_indom_both.
  }
  specialize (H Hhead). clear Hhead.

  destruct H as (h'' & hv & H & Hh'').
  pose proof (@Fmap.remove_update_self _ _ _ _ _ E) as Hself.
  rewrite -> update_eq_union_single in Hself.
Abort.
*)

(*
Lemma hmerge_split Q p d :
  let Q' := fun h => 
  forall v : int, hmerge val_int_add Q (hsingle p d v) ==>
    hexists (fun diff : int =>
      hstar Q' (hsingle p d (val_int_add v (val_int diff)))).
Proof.

Lemma hmerge_split Q p d :
  forall v : int, hmerge val_int_add Q (hsingle p d v) ==>
    hexists (fun Q' => hexists (fun diff : int =>
      hstar Q' (hsingle p d (val_int_add v (val_int diff))))).
Proof.
  intros.
  hnf. intros h Hh.
  unfold hmerge in Hh. destruct Hh as (h1 & h2 & H1 & H2 & E).
  apply hsingle_inv in H2.
  (* now ask *)
  destruct (fmap_data h1 (p, d)) eqn:E1.
  { destruct (match v0 with val_int _ => true | _ => false end) eqn:E2.
    { destruct v0; try eqsolve.

      

  hexists_intro
  
*)

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
Proof using.
  clear N M Lval Lind H_length_Lval H_length_Lind 
    H_Lval_notnil H_Lind_last H_Lind_inc H_Lind_first.

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
Proof using.
  clear N M Lval Lind H_length_Lval H_length_Lind 
    H_Lval_notnil H_Lind_last H_Lind_inc H_Lind_first.

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
        (label (Lab (pair 2 0) (interval 0 N)))) \* \Top) hv).
Proof.
  intros.
  rewrite -> Union_localization.
  2:{
    intros i j Hii Hjj H. unfold ind_seg. 
    rewrite -> indom_interval in Hii, Hjj.
    destruct Hii as (Hii1 & Hii2), Hjj as (Hjj1 & Hjj2).
    (* TODO extract this? *)
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
  }
  eapply xfor_big_op_lemma with
    (Inv:=fun=> arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
      arr_x_val px_val (⟨(1, 0), 0⟩)%arr \* \Top)
    (* need \Top to consume some memory *)
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
  2:{
    apply fm_localization.

    (* repeat *)
    intros i j Hii Hjj H. unfold ind_seg. 
    rewrite -> indom_interval in Hii, Hjj.
    destruct Hii as (Hii1 & Hii2), Hjj as (Hjj1 & Hjj2).
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
  }
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
    2:{
      (* repeat *)
      intros i j Hii Hjj H. unfold ind_seg. 
      rewrite -> indom_interval in Hii, Hjj.
      destruct Hii as (Hii1 & Hii2), Hjj as (Hjj1 & Hjj2).
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
    }

    rewrite <- interval_segmentation.
    xsimpl.
  }
  (* post *)
  2:{
    intros. xsimpl.
    rewrite -> hstars_pick_last_4. 
    eapply himpl_trans.
    1: apply himpl_frame_l.
    2: apply himpl_frame_r; xsimpl.
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
          arr_x_val px_val (Lab (2, 0) (eld d)))) \* \Top).
    2: xsimpl.
    1:{
      eapply htriple_conseq.
      1: apply htriple_union_pointwise with (Q:=
        fun d hv => 
            \[hv d = val_int (nth (abs l) Lval)] \*
            arr_x_ind px_ind d \* arr_x_val px_val d \* \Top).
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
    xsimpl. intros r. rewrite <- hstar_hempty_r at 1.
    eapply himpl_frame_lr. 2: xsimpl.
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

Lemma htriple_sequ2 (fs fs' : fset D) H Q' Q ht ht1 ht2 htpre ht'
  (Hdj : disjoint fs fs')
  (Hhtpre : forall d, indom fs d -> htpre d = ht1 d)
  (Hhtpre' : forall d, indom fs' d -> htpre d = ht' d)
  (Htppre : htriple (fs \u fs') htpre H Q') (* hv? *)
  (Hht : forall d, indom fs d -> ht d = trm_seq (ht1 d) (ht2 d))
  (Hht' : forall d, indom fs' d -> ht d = ht' d)
  (Htp2 : forall hv, htriple fs ht2 (Q' hv) (fun hr => Q (uni fs hr hv)))
  (Hcong : forall hv1 hv2, (forall d, indom (fs \u fs') d -> hv1 d = hv2 d) -> 
    Q hv1 ==> Q hv2) :
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
  hnf. intros. apply wp_equiv. 
  eapply htriple_conseq.
  1: apply Htp2.
  1: xsimpl.
  hnf. intros. apply Hcong.
  intros d Hu. rewrite -> indom_union_eq in Hu. unfold uni. 
  repeat case_if; try eqsolve.
  exfalso. revert C C0. apply disjoint_inv_not_indom_both. 
  apply Hdj.
Qed.

Lemma ntriple_sequ2 (fs fs' : fset _) H Q' Q
  (ht' ht1 ht2 : _ -> trm) (i j : int) (Hij : i <> j)
  (Htppre : 
    ntriple H
      (Lab (pair i 0) (FH fs ht1) :: 
       Lab (pair j 0) (FH fs' ht') :: nil)
    Q')
  (Htp2 : forall hv, 
    htriple (label (Lab (pair i 0) fs)) (fun d => ht2 (eld d)) 
      (Q' hv) (fun hr => Q (uni (label (Lab (pair i 0) fs)) hr hv)))
  (Hcong : forall hv1 hv2, 
    (forall d, 
      indom ((label (Lab (pair i 0) fs)) \u (label (Lab (pair j 0) fs'))) d -> 
      hv1 d = hv2 d) -> 
    Q hv1 ==> Q hv2)
  :
  ntriple H
    (Lab (pair i 0) (FH fs (fun d => trm_seq (ht1 d) (ht2 d))) :: 
     Lab (pair j 0) (FH fs' ht') :: nil)
    Q.
Proof using.
  unfold ntriple, nwp.
  simpl fset_of. rewrite -> union_empty_r.
  erewrite -> wp_ht_eq.
  1: apply wp_equiv.
  1: eapply htriple_sequ2 with 
    (ht1:=fun d => ht1 (eld d))
    (ht2:=fun d => ht2 (eld d))
    (htpre:=uni (label (Lab (pair i 0) fs)) (fun d => ht1 (eld d))
      (uni (label (Lab (pair j 0) fs')) (fun d => ht' (eld d)) (fun=> val_unit)))
    (ht:=uni (label (Lab (pair i 0) fs)) (fun d => trm_seq (ht1 (eld d)) (ht2 (eld d)))
      (uni (label (Lab (pair j 0) fs')) (fun d => ht' (eld d)) (fun=> val_unit)))
    (ht':=fun d => ht' (eld d)).
  1:{
    apply disjoint_of_not_indom_both.
    intros (ll, d) H1 H2. apply indom_label in H1, H2. eqsolve.
  }
  1:{
    intros. unfold uni. case_if; try reflexivity. contradiction.
  }
  1:{
    intros. unfold uni. case_if.
    1:{ destruct d as (ll, d). apply indom_label in H0, C. eqsolve. }
    case_if; try contradiction. reflexivity.
  }
  2:{
    intros. unfold uni. case_if; try reflexivity. contradiction.
  }
  2:{
    intros. unfold uni. case_if.
    1:{ destruct d as (ll, d). apply indom_label in H0, C. eqsolve. }
    case_if; try contradiction. reflexivity.
  }
  3: apply Hcong.
  3:{
    intros. destruct d as (ll, d).
    rewrite -> indom_union_eq, -> ! indom_label_eq in H0.
    destruct H0 as [ (<- & Hin) | (<- & Hin) ].
    { unfold htrm_of, uni. simpl. case_if; try eqsolve.
      rewrite -> ! indom_label_eq.
      case_if; eqsolve.
    }
    { unfold htrm_of, uni. simpl. case_if; try eqsolve.
      rewrite -> ! indom_label_eq.
      repeat case_if; try eqsolve.
    }
  }
  2: apply Htp2.
  unfold ntriple, nwp in Htppre.
  simpl fset_of in Htppre. rewrite -> union_empty_r in Htppre.
  apply wp_equiv.
  erewrite -> wp_ht_eq in Htppre.
  1: apply Htppre.

  (* repeat? *)
  intros. destruct d as (ll, d).
  rewrite -> indom_union_eq, -> ! indom_label_eq in H0.
  destruct H0 as [ (<- & Hin) | (<- & Hin) ].
  { unfold htrm_of, uni. simpl. case_if; try eqsolve.
    rewrite -> ! indom_label_eq.
    case_if; eqsolve.
  }
  { unfold htrm_of, uni. simpl. case_if; try eqsolve.
    rewrite -> ! indom_label_eq.
    repeat case_if; try eqsolve.
  }
Qed.

Lemma rlsum_rli_ntriple : forall (px_ind px_val : loc),
  ntriple 
    ((\*_(d <- ⟨pair 1 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
     (\*_(d <- ⟨pair 2 0, interval 0 N⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))))
    ((Lab (pair 1 0) (FH (single 0 tt) (fun=> (rlsum_func px_ind px_val)))) :: 
      (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => \[hv (Lab (pair 1 0) 0) = 
      fset_fold (val_int 0) 
        (fun d acc => val_int_add acc (hv d))
        (label (Lab (pair 2 0) (interval 0 N)))] \* \Top).
Proof.
  intros.
  unfold rlsum_func.
  (* simplify 1 first *)
  apply (xfocus_lemma (pair 1 0)); simpl; try apply xnwp0_lemma.
  rewrite -> union_empty_r.
  (* little change *)
  rewrite -> wp_ht_eq with (ht2:=(fun=> (rlsum_func px_ind px_val))).
  2:{ intros. unfolds label. 
    (* coercion: eld *)
    (* TODO extract this out to be a lemma *)
    rewrite -> indom_Union in H. 
    setoid_rewrite -> indom_single_eq in H.
    destruct H as (? & <- & <-).
    simpl. rewrite -> indom_single_eq. case_if. auto.
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
    fun=> trm_seq (For 0 M (trm_fun "i" (rlsum_loopbody px_ind px_val ps0 "i"))) (<{ ! ps0 }>)).
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
  simpl. eapply htriple_conseq_frame with (H2:=\Top).
  1: apply htriple_get.
  1: apply himpl_frame_l.
  1: xsimpl.
  1: match goal with |- himpl (hsingle _ _ ?vv) _ => instantiate (1:=fun=> vv) end.
  1: apply himpl_refl.
  hnf. intros.
  xsimpl. intros ->.
  unfold uni. rewrite -> indom_label_eq, indom_single_eq. case_if; try eqsolve.
  apply fold_fset_eq.
  intros. extens. intros. case_if; try reflexivity.
  destruct d as (ll, d). apply indom_label in H, C7. eqsolve.
Qed.

End Demo.
