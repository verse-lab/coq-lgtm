Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer.
From SLF Require Import Struct Loops Unary_IndexWithBounds SV2 Subst.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Definition to_int (v : val) : int := 
  match v with 
  | val_int i => i 
  | _ => 0
  end.

Coercion to_int : val >-> Z.

(* Module Export AD := WithUnary(Int2Dom). *)

Module csr.

Import sv.

Section csr.

Notation "'mval'" := ("m_val":var) (in custom trm at level 0) : trm_scope.
Notation "'colind'" := ("col_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'rowptr'" := ("row_ptr":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Import List Vars.

Context (mval colind rowptr : list int).
Context (N Nrow Ncol : int).
Hypothesis Nrow_nonneg : 0 <= Nrow.
Hypothesis len_mval : length mval = N :> int.
Hypothesis len_colind : length colind = N :> int.
Hypothesis len_rowptr : length rowptr = Nrow + 1 :> int.
Hypothesis colind_leq : forall x, In x colind -> 0 <= x < Ncol.
Hypothesis rowptr_first : List.nth (abs 0) rowptr 0 = 0.
Hypothesis rowptr_last : List.nth (abs Nrow) rowptr 0 = N.
Hypothesis rowptr_weakly_sorted : forall (i j : int), 
  (0 <= i <= Nrow) -> 
  (0 <= j <= Nrow) -> 
  (i <= j) -> 
  (List.nth (abs i) rowptr 0 <= List.nth (abs j) rowptr 0).

Definition colind_seg (row : int) :=
  list_interval (abs (nth (abs row) rowptr 0)) (abs (nth (abs (row + 1)) rowptr 0)) colind.

Hypothesis nodup_eachcol : forall x : int, 0 <= x < Nrow -> NoDup (colind_seg x).
(* FIXME: rowptr may not be strictly increasing? so the existing definition of increasing list 
    may not work, currently use these instead *)

Tactic Notation "seclocal_solver" :=
  first [ assumption 
    | rewrite -/(colind_seg _); now apply nodup_eachcol
    | (* for rowptr[?] <= N *)
      try rewrite -> len_colind; try rewrite -> len_mval; 
      try rewrite <- rowptr_last; apply rowptr_weakly_sorted; math
    | (* for 0 <= rowptr[?] *)
      rewrite <- rowptr_first at 1; apply rowptr_weakly_sorted; math
    | (* for 0 <= rowptr[i] <= rowptr[i + 1] *)
      split; [ rewrite <- rowptr_first at 1 | ]; apply rowptr_weakly_sorted; math
    | idtac ]; auto.

(* Definition indexf := index_bounded.func. *)

Definition csrij := 
<{
  fun mval colind rowptr i j =>
    let "lb" = read_array rowptr i in
    let "ii" = i + 1 in
    let "rb" = read_array rowptr "ii" in
    (* let k = indexf "lb" "rb" j colind in
    let c = k < "rb" in
    if c
    then 
      let "tmp" = read_array mval k in "tmp"
    else 0 *)
    sv.get j colind mval "lb" "rb"
}>.

Lemma csrij_spec_in {D : Type} `{Inhab D} (x_mval x_colind x_rowptr : loc) (i j : int) d : 
  @htriple D (single d tt) 
    (fun=> csrij x_mval x_colind x_rowptr i (nth (abs j) (colind_seg i) 0))
    (\[0 <= i < Nrow] \*
      \[0 <= j < (nth (abs (i + 1)) rowptr 0) - (nth (abs i) rowptr 0)] \*
      harray_int mval x_mval d \* 
      harray_int colind x_colind d \* 
      harray_int rowptr x_rowptr d)
    (fun hr => 
     \[hr = fun=> List.nth (abs ((nth (abs i) rowptr 0) + j)) mval 0] \* 
      harray_int mval x_mval d \* 
      harray_int colind x_colind d \* 
      harray_int rowptr x_rowptr d).
Proof with seclocal_solver.
  rewrite -wp_equiv; xsimpl=> ??.
  do 3 (xwp; xapp).
  rewrite /colind_seg.
  xapp get_spec_in; eauto... 
  rewrite <- list_interval_nth... xsimpl*.
Qed.

Lemma csrij_spec_out_unary {D : Type} `{Inhab D} (x_mval x_colind x_rowptr : loc) (i j : int) d :
  @htriple D (single d tt) 
    (fun=> csrij x_mval x_colind x_rowptr i j)
    (\[0 <= i < Nrow /\ ~ In j (colind_seg i)] \*
      harray_int mval x_mval d \* 
      harray_int colind x_colind d \* 
      harray_int rowptr x_rowptr d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      harray_int mval x_mval d \* 
      harray_int colind x_colind d \* 
      harray_int rowptr x_rowptr d).
Proof with seclocal_solver.
  rewrite -wp_equiv; xsimpl=> ?.
  do 3 (xwp; xapp).
  xapp get_spec_out_unary; eauto...
  1: now unfold colind_seg in *.
  xsimpl*.
Qed.

(* here lb and rb are not fixed, so cannot directly apply get_spec_out *)
Lemma csrij_spec_out `{Inhab (labeled (int * int))} fs (x_mval x_colind x_rowptr : loc) : 
  @htriple (labeled (int * int)) fs
    (fun d => csrij x_mval x_colind x_rowptr (eld d).1 (eld d).2)
    (\[forall d, indom fs d -> 0 <= (eld d).1 < Nrow /\ ~ In (eld d).2 (colind_seg (eld d).1)] \*
      (\*_(d <- fs) harray_int mval x_mval d) \* 
      (\*_(d <- fs) harray_int colind x_colind d) \* 
       \*_(d <- fs) harray_int rowptr x_rowptr d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      (\*_(d <- fs) harray_int mval x_mval d) \*
      (\*_(d <- fs) harray_int colind x_colind d) \*  
       \*_(d <- fs) harray_int rowptr x_rowptr d).
Proof.
  apply/htriple_val_eq/htriple_conseq;
  [|eauto|move=> ?]; rewrite -hstar_fset_pure -?hbig_fset_hstar; first last.
  { move=> ?; apply: applys_eq_init; reflexivity. }
  apply/htriple_union_pointwise=> [> -> //|[?][??]?]. 
  rewrite -wp_equiv wp_single. 
  xapp (@csrij_spec_out_unary (labeled (int * int)))=> //= ??->.
  xsimpl*.
Qed.

Definition csrsum := 
  <{
  fun mval colind rowptr =>
  let s = ref 0 in
  (* 
  for i <- [0, N] {
    let x = mval[i] in 
    s += x
  }; 
  *)
  for i <- [0, Nrow] {
    let "lb" = read_array rowptr i in
    let "ii" = i + 1 in
    let "rb" = read_array rowptr "ii" in
    let x = sv.sum colind mval "lb" "rb" in 
    s += x
  };
  ! s
}>.

Tactic Notation "seclocal_fold" := 
  rewrite ?label_single ?wp_single
    -/(For_aux _ _) 
    -/(For _ _ _) //=.


Lemma htriple_letu2 {D : Type} (fs fs' : fset _) H Q' Q ht ht1 ht2 htpre ht' x
  (Hdj : disjoint fs fs')
  (Hhtpre : forall d, indom fs d -> htpre d = ht1 d)
  (Hhtpre' : forall d, indom fs' d -> htpre d = ht' d)
  (Htppre : htriple (fs \u fs') htpre H Q') (* hv? *)
  (Hht : forall d, indom fs d -> ht d = trm_let (x d) (ht1 d) (ht2 d))
  (Hht' : forall d, indom fs' d -> ht d = ht' d)
  (Htp2 : forall hv, htriple fs (fun d => subst (x d) (hv d) (ht2 d)) (Q' hv) (fun hr => Q (uni fs' hv hr))) :
  (* (Hcong : forall hv1 hv2, (forall d, indom (fs \u fs') d -> hv1 d = hv2 d) -> 
    Q hv1 ==> Q hv2) : *)
  @htriple D (fs \u fs') ht H Q.
Proof using All.
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
    1: apply wp_let.
    rewrite -> wp_ht_eq with (ht1:=ht) (ht2:=fun d => trm_let (x d) (ht1 d) (ht2 d)).
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
  (*   have {}Htppre: H ==> wp fs' htpre (fun=> wp fs htpre Q').
  { apply: himpl_trans; last apply:wp_union2; autos*. }
  (* 2: rewrite -> disjoint_comm; apply Hdj. *)
  eapply himpl_trans.
  1: apply Htppre.
  apply wp_conseq.
  hnf. intros. apply wp_conseq.
  hnf. intros. 
  xapp=> hv.
  move=> ?; apply:applys_eq_init; f_equal; extens=> ?; rewrite /uni.
  do? case:classicT=> //. *)
  erewrite wp_ht_eq.
  { xapp=> hv. 
    move=> ?; apply:applys_eq_init; f_equal; extens=> ?; rewrite /uni.
    do? case:classicT=> //. } 
  move=> ? IN /=. 
  rewrite /uni; case: classicT=> // /(disjoint_inv_not_indom_both _ IN).
  case; autos*.
Qed.

Lemma ntriple_letu2 {D : Type} (s : _) H Q' Q fsht x
  (t1 t2 : trm) (i : int)
  (Htppre : 
    ntriple H
      (Lab (pair i 0) (FH (`{s}) (fun=>t1)) :: 
       fsht)
    Q')
  (Htp2 : forall hv, 
    htriple (label (Lab (pair i 0) (`{s}))) (fun d => subst x (hv[`i](s)) t2) 
      (Q' hv) (fun hr => Q (uni (fset_of fsht) hv hr)))
  :
  ~ has_lab fsht (i,0) ->
  @ntriple D H
    (Lab (pair i 0) (FH (`{s}) (fun d => trm_let x t1 t2)) :: 
    fsht)
    Q.
Proof using All.
  (* move/hasnt_lab. *)
  move=> HNL.
  unfold ntriple, nwp.
  simpl fset_of.
  erewrite -> wp_ht_eq.
  1: apply wp_equiv.
  1: eapply htriple_letu2 with 
    (ht1:=fun=> t1)
    (ht2:=fun=> t2)
    (htpre:=uni (label (Lab (pair i 0) (`{s}))) (fun=> t1)
      (htrm_of fsht))
    (ht:=uni (label (Lab (pair i 0) (`{s}))) (fun d => trm_let x t1 t2)
      (htrm_of fsht))
    (ht':=htrm_of fsht).
  { rewrite (hasnt_lab _ _ HNL); exact/fset_htrm_label_remove_disj. }
  { intros. unfold uni. case_if; try reflexivity. contradiction. }
  { move=> ?; rewrite (hasnt_lab _ _ HNL) /uni; case: classicT=> //.
    move=>/(@disjoint_inv_not_indom_both _ _ _ _ _)/[apply]-[].
    exact/fset_htrm_label_remove_disj. }
  2:{
    intros. unfold uni. case_if; try reflexivity. contradiction.
  }
  2:{ move=> ?; rewrite (hasnt_lab _ _ HNL) /uni; case: classicT=> //.
    move=>/(@disjoint_inv_not_indom_both _ _ _ _ _)/[apply]-[].
    exact/fset_htrm_label_remove_disj. }
  3:{ case=> *; by rewrite /uni /= indom_label_eq. }
  2: { move=> hr /=. 
    rewrite -wp_equiv label_single wp_single -label_single wp_equiv.
    apply/Htp2. }
  unfold ntriple, nwp in Htppre.
  simpl fset_of in Htppre.
  apply wp_equiv.
  erewrite -> wp_ht_eq in Htppre.
  1: apply Htppre.

  intros d H0. destruct d as (ll, d).
  rewrite -> indom_union_eq, -> ! indom_label_eq in H0. 
  unfold htrm_of, uni. rewrite ! indom_label_eq. simpl. repeat case_if; try eqsolve.
Qed.

Lemma xletu2 {D : Type} (s : _) H Q' Q fsht x
  (t1 t2 : trm) (i : int)
  (Htppre : 
    ntriple H
      (Lab (pair i 0) (FH (`{s}) (fun=>t1)) :: 
       fsht)
    Q')
  (Htp2 : forall hv, 
    htriple (label (Lab (pair i 0) (`{s}))) (fun d => subst x (hv[`i](s)) t2) 
      (Q' hv) (fun hr => Q (lab_fun_upd hr hv (i,0))))
  :
  ~ has_lab fsht (i,0) ->
  @ntriple D H
    (Lab (pair i 0) (FH (`{s}) (fun d => trm_let x t1 t2)) :: 
    fsht)
    Q.
Proof.
  move=> ?; apply/ntriple_letu2; eauto=> hv.
  rewrite -wp_equiv -/(fs_of (FH (`{s}) (fun=> subst x (hv[`i](s)) t2))).
  rewrite -/(ht_of (FH (`{s}) (fun=> subst x (hv[`i](s)) t2))) xnwp1_lemma /=.
  rewrite -xnwp1_lemma/=; apply:himpl_trans; last exact/wp_hv.
  xapp=> hr. xsimpl (lab_fun_upd hr hv (i,0))=> ?; apply:applys_eq_init; f_equal.
  extens=> -[??] /=; rewrite /uni; case: classicT.
  { erewrite (hasnt_lab fsht); eauto=> /(@indom_remove _ _ _ _ _)=> lN.
    case E: (lab_eqb _ _)=> //; move: lN; rewrite -lab_eqbE E //. }
  case: classicT=> //; rewrite indom_label_eq indom_single_eq=> -[]->.
  by rewrite eqbxx.
Qed.

Lemma xnapp_lemma' : forall {D : Type} fs_ht Q1 H1 H Q,
  ntriple H1 fs_ht Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  @ntriple D H fs_ht Q.
Proof using.
  introv tE M W.
  apply/xapp_lemma; autos*.
  by rewrite -wp_equiv.
Qed.

Lemma wp_prod_single {A B : Type} s fs Q ht (l : labType):
  @wp (labeled (A * B)) (label (Lab l (`{s} \x fs))) ht Q = 
  @wp (labeled (A * B)) (label (Lab l (`{s} \x fs))) (fun ld => ht(Lab l (s, (eld ld).2))) Q.
Proof.
Admitted.

Tactic Notation "xnapp" constr(E) := 
  rewrite -> ?hbig_fset_hstar;
  apply/xletu2=> //=; [eapply xnapp_lemma'; 
       [eapply E|
         let hp := fresh "hp" in 
         let HE := fresh "HE" in 
        remember hpure as hp eqn:HE;
       xapp_simpl=> ?; rewrite HE; exact: himpl_refl]|]; eauto; simpl.

Lemma in_interval_list {A : Type} (l : list A) lb rb x: 
   In x (list_interval lb rb l) -> In x l.
Proof.
Admitted.
Arguments in_interval_list {_ _ _ _ _}.

Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition eld := @LibWP.eld (int * int)%type.
Coercion eld : D >-> Dom.

Lemma csrsum_spec `{Inhab D} (x_mval x_colind x_rowptr : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}   => csrsum x_mval x_colind x_rowptr];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => csrij x_mval x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) hv[`2](i)] \* \Top}}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver).
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : xwp; xapp=> s...
  assert (`[0, Nrow] \x `[0, Ncol] = Union `[0, Nrow] (fun i => `{i} \x `[0, Ncol])) as E
    by now rewrite prod_cascade.
  rewrite E.
  set (R i := 
    arr(x_mval, mval)⟨2, i⟩ \*
    arr(x_colind, colind)⟨2, i⟩ \* 
    arr(x_rowptr, rowptr)⟨2, i⟩ : hhprop D).
  set (Inv (i : int) := 
    arr(x_mval, mval)⟨1, (0,0)⟩ \* 
    arr(x_colind, colind)⟨1, (0,0)⟩ \* 
    arr(x_rowptr, rowptr)⟨1, (0,0)⟩).
  xfor_sum Inv R R (fun hv i => Σ_(j <- `{i} \x `[0, Ncol]) hv[`2](j)) s.
  { rewrite /Inv /R.
    xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xframe2 (arr(x_rowptr, rowptr)⟨1, (0, 0)⟩).
    xsubst (snd : _ -> int).
    rewrite fsubst_single /=. rewrite -> prod_fsubst_snd with (a:=l0)...
    rewrite (@hstar_fset_eq_restr _ _ _ (fun d => arr(x_mval, mval)⟨2, d⟩ \\*
      arr(x_colind, colind)⟨2, d⟩ \\*
      arr(x_rowptr, rowptr)⟨2, d⟩) (`{l0} \x `[0, Ncol]) snd).
    2:{ hnf. intros (?, ?) (?, ?) HH1 HH2. rewrite ?indom_prod ?indom_single_eq /= in HH1, HH2 |- * =>?. eqsolve. }
    rewrite -> prod_fsubst_snd with (a:=l0)...
    xnapp sv.sum_spec...
    { move=> ?/in_interval_list... }
    move=> ?; rewrite -wp_equiv. xsimpl=>->.
    (* TODO weird. xapp (@incr.spec _ H) does not work here; try something else first *)
    assert (Inhab (labeled int)) as H_ by (constructor; now exists (Lab (0,0) 0)).
    apply wp_equiv. eapply htriple_conseq_frame.
    1: eapply incr.spec. xsimpl*. xsimpl*.
    (* weird *)
    unfold prod. rewrite <- SumCascade, -> Sum1, <- SumCascade.
    { erewrite SumEq with (fs:=`[0, Ncol]). 1: xsimpl*.
      intros c Hin. simpl. now rewrite Sum1. } 
    { intros i0 j0 Hneq _ _. apply disjoint_of_not_indom_both.
      intros (r, c). rewrite !indom_single_eq /=. congruence. }
    { intros i0 j0 Hneq Ha Hb. rewrite !indom_single_eq in Ha, Hb. congruence. } }
  { intros Hneq Hi Hj. 
    apply disjoint_of_not_indom_both.
    intros (r, c). rewrite !indom_prod !indom_interval !indom_single_eq /=. math. }
  { now rewrite !indom_prod !indom_interval !indom_single_eq /= in someindom. }
  { xapp. xsimpl*. rewrite SumCascade; try reflexivity.
    (* repeating the proof above? *)
    intros i0 j0 Hneq. rewrite ! indom_interval=> ? ?.
    apply disjoint_of_not_indom_both.
    intros (r, c). rewrite !indom_prod !indom_interval !indom_single_eq /=. math. }
Qed.

Context (dvec : list int).
Context (dvec_len : length dvec = Ncol :> int).

Definition csrspmv := 
  <{
  fun mval colind rowptr dvec =>
  let s = ref 0 in
  for i <- [0, Nrow] {
    let "lb" = read_array rowptr i in
    let "ii" = i + 1 in
    let "rb" = read_array rowptr "ii" in
    let x = sv.dotprod colind mval dvec "lb" "rb" in 
    s += x
  };
  ! s
}>.

Lemma csrspmv_spec `{Inhab D} (x_mval x_colind x_rowptr x_dvec : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     arr(x_dvec, dvec)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_dvec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}                 => csrspmv x_mval x_colind x_rowptr x_dvec];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => csrij x_mval x_colind x_rowptr ld.1 ld.2}
  }]
  (* is this a good way to describe matrix-vector multiplication? *)
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) (hv[`2](i) * dvec[i.2])] \* \Top}}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver).
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : xwp; xapp=> s...
  assert (`[0, Nrow] \x `[0, Ncol] = Union `[0, Nrow] (fun i => `{i} \x `[0, Ncol])) as E
    by now rewrite prod_cascade.
  rewrite E.
  set (R i := 
    arr(x_mval, mval)⟨2, i⟩ \*
    arr(x_colind, colind)⟨2, i⟩ \* 
    arr(x_rowptr, rowptr)⟨2, i⟩ \*
    arr(x_dvec, dvec)⟨2, i⟩ : hhprop D).
  set (Inv (i : int) := 
    arr(x_mval, mval)⟨1, (0,0)⟩ \* 
    arr(x_colind, colind)⟨1, (0,0)⟩ \* 
    arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
    arr(x_dvec, dvec)⟨1, (0,0)⟩).
  xfor_sum Inv R R (fun hv i => Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * dvec[j.2])) s.
  { rewrite /Inv /R.
    xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xframe2 (arr(x_rowptr, rowptr)⟨1, (0, 0)⟩).
    xsubst (snd : _ -> int).
    rewrite fsubst_single /=. rewrite -> prod_fsubst_snd with (a:=l0)...
    rewrite (@hstar_fset_eq_restr _ _ _ (fun d => arr(x_mval, mval)⟨2, d⟩ \\*
      arr(x_colind, colind)⟨2, d⟩ \\*
      arr(x_rowptr, rowptr)⟨2, d⟩ \\* arr(x_dvec, dvec)⟨2, d⟩) (`{l0} \x `[0, Ncol]) snd).
    2:{ hnf. intros (?, ?) (?, ?) HH1 HH2. rewrite ?indom_prod ?indom_single_eq /= in HH1, HH2 |- * =>?. eqsolve. }
    rewrite -> prod_fsubst_snd with (a:=l0)...
    xnapp sv.dotprod_spec...
    { move=> ?/in_interval_list... }
    move=> ?; rewrite -wp_equiv. xsimpl=>->.
    (* TODO weird. xapp (@incr.spec _ H) does not work here; try something else first *)
    assert (Inhab (labeled int)) as H_ by (constructor; now exists (Lab (0,0) 0)).
    apply wp_equiv. eapply htriple_conseq_frame.
    1: eapply incr.spec. xsimpl*. xsimpl*.
    (* weird *)
    unfold prod. rewrite <- SumCascade, -> Sum1, <- SumCascade.
    { erewrite SumEq with (fs:=`[0, Ncol]). 1: xsimpl*.
      intros c Hin. simpl. now rewrite Sum1. } 
    { intros i0 j0 Hneq _ _. apply disjoint_of_not_indom_both.
      intros (r, c). rewrite !indom_single_eq /=. congruence. }
    { intros i0 j0 Hneq Ha Hb. rewrite !indom_single_eq in Ha, Hb. congruence. } }
  { intros Hneq Hi Hj. 
    apply disjoint_of_not_indom_both.
    intros (r, c). rewrite !indom_prod !indom_interval !indom_single_eq /=. math. }
  { now rewrite !indom_prod !indom_interval !indom_single_eq /= in someindom. }
  { xapp. xsimpl*. rewrite SumCascade; try reflexivity.
    (* repeating the proof above? *)
    intros i0 j0 Hneq. rewrite ! indom_interval=> ? ?.
    apply disjoint_of_not_indom_both.
    intros (r, c). rewrite !indom_prod !indom_interval !indom_single_eq /=. math. }
Qed.

End csr.

End csr.
