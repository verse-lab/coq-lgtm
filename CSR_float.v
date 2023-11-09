Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer ListCommon.
From SLF Require Import Struct Loops Unary Subst NTriple Loops2 Struct2 Loops2_float Struct SV_float.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Module csr.

Section csr.

Notation "'mval'" := ("m_val":var) (in custom trm at level 0) : trm_scope.
Notation "'colind'" := ("col_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'rowptr'" := ("row_ptr":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
Notation "'lb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'rb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.
Notation "'i''" := ("i_'":var) (in custom trm at level 0) : trm_scope.

Import List Vars.

Context (mval : list binary64).
Context (colind rowptr : list int).
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
Hypothesis mval_finite : forall x, In x mval -> @finite Tdouble x.

Definition colind_seg (row : int) :=
  list_interval (abs (nth (abs row) rowptr 0)) (abs (nth (abs (row + 1)) rowptr 0)) colind.

Hypothesis nodup_eachcol : forall x : int, 0 <= x < Nrow -> NoDup (colind_seg x).
Hypothesis sorted_eachcol : forall x : int, 0 <= x < Nrow -> sorted (colind_seg x). (* TODO possibly remove nodup_eachcol since sorted_eachcol subsumes it? *)
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
      (* TODO this could be better? *)
    | intros; eapply colind_leq, in_interval_list; now eauto
    | intros; eapply mval_finite, in_interval_list; now eauto
    | idtac ]; auto.

(* Definition indexf := index_bounded.func. *)

Definition get := 
<{
  fun mval colind rowptr i j =>
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
      sv_float.get j colind mval lb rb
}>.
(*
Definition sum := 
  <{
  fun mval colind rowptr =>
  let s = ref 0 in
  for i <- [0, Nrow] {
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
    let x = sv.sum colind mval lb rb in 
      s += x
  };
  ! s
}>.
*)
Tactic Notation "seclocal_fold" := 
  rewrite ?label_single ?wp_single
    -?/(harray_float _ _ _)
    -?/(harray_int _ _ _)
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Arguments in_interval_list {_ _ _ _ _}.

Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition eld := @LibWP.eld (int * int)%type.
Coercion eld : D >-> Dom.
(*
Lemma sum_prod1{A B :Type} (fs : fset B) (x : A) : 
  Sum (`{x} \x fs) = fun Q => Sum fs (fun i => Q (x, i)).
Proof.
  extens=> ?.
  unfold prod; rewrite -SumCascade ?Sum1 -?SumCascade; try by disjointE.
  erewrite SumEq with (fs:=fs); eauto.
  move=>* /=; by rewrite Sum1.
Qed.

Lemma sum_prod1' {A B :Type} (fs : fset B) Q: 
(fun x : A => Sum (`{x} \x fs) Q) = fun x => Sum fs (fun i => Q (x, i)).
Proof.
extens=> ?.
unfold prod; rewrite -SumCascade ?Sum1 -?SumCascade; try by disjointE.
erewrite SumEq with (fs:=fs); eauto.
move=>* /=; by rewrite Sum1.
Qed.

Definition sum_prod1E := (@sum_prod1, @sum_prod1')%type.
*)
(*
Lemma sum_spec `{Inhab D} (x_mval x_colind x_rowptr : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}   => sum x_mval x_colind x_rowptr];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) hv[`2](i)] \* \Top}}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver).
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : xwp; xapp=> s...
  rewrite prod_cascade.
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
    xnapp sv.sum_spec...
    { move=> ?/in_interval_list... }
    move=> ?; rewrite -wp_equiv. xsimpl=>->.
    xapp @incr.spec; rewrite sum_prod1E; xsimpl. }
  { xapp. xsimpl*. rewrite SumCascade //; disjointE. }
Qed.
*)
Context (dvec : list binary64).
Context (dvec_len : length dvec = Ncol :> int).
Hypothesis dvec_finite : forall x, In x dvec -> @finite Tdouble x.

Definition spmv := 
  <{
  fun mval colind rowptr dvec =>
  let s = allocf0 Nrow in
  for i <- [0, Nrow] {
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
    let x = sv_float.dotprod colind mval dvec lb rb in 
    val_array_set s i x
  }; 
  s
}>.

Lemma spmv_spec `{Inhab D} (x_mval x_colind x_rowptr x_dvec : loc) : 
  {{ .arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     .arr(x_dvec, dvec)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) .arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) .arr(x_dvec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}                 => spmv x_mval x_colind x_rowptr x_dvec];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, (\exists p, \exists vl : int -> binary64, 
    \[hv[`1]((0,0)) = val_loc p /\ forall i : int, 0 <= i < Nrow ->
      @feq Tdouble (vl i) (Sum_fma float_unit (lof id Ncol) (fun j => (to_float (hv[`2]((i, j))), dvec[j])))] \*
    harray_fun_float vl p Nrow (Lab (1,0) (0,0)))
      \* \Top }}. (* this \Top can be made concrete, if needed *)
Proof with (try solve [ seclocal_solver ]; seclocal_fold).
  xset_Inv Inv 1; xset_R int Inv R 2.
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : (xwp; xapp (@htriple_allocf0_unary)=> // s)...
  rewrite prod_cascade.
  xfor_specialized_normal_float Inv R R (fun hv i => (Sum_fma float_unit (lof id Ncol) (fun j => (to_float (hv[`2]((i, j))), dvec[j])))) (fun=> float_unit) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xsubst (snd : _ -> int)...
    xnapp sv_float.dotprod_spec hv...
    xsimpl=>Hfeq. xapp @lhtriple_array_set_pre; try math.
    xsimpl (to_float (hv[`1](0))); move: Hfeq; rewrite /feq_val;
    destruct (hv[`1](0))=> //. }
  { apply Sum_fma_feq=>? /In_lof_id ? /=. split; auto. rewrite hvE //; autorewrite with indomE; simpl; split; auto; try math. }
  { xwp; xval. xsimpl*. }
Qed.

Section spmv_monolithic.

Import Loops_float.

(* simulating the crs_matrix_vector_multiply function in LAProof *)
Definition spmv_monolithic := 
  <{
  fun mval colind rowptr dvec =>
  let "ans" = allocf0 Nrow in
  let "row_ptr[0]" = read_array rowptr 0 in
  let "next" = ref "row_ptr[0]" in
  for i <- [0, Nrow] {
    let s = ref float_unit in
    let h = ! "next" in
    let "i + 1" = i + 1 in
    let "row_ptr[i + 1]" = read_array rowptr "i + 1" in
    "next" := "row_ptr[i + 1]";
    for j <- [h, "row_ptr[i + 1]"] {
      let x = mval[.j] in 
      let c = colind[j] in 
      let v = dvec[.c] in 
      fma.func s x v
    };
    let "res" = ! s in
    free s;
    val_array_set "ans" i "res"
  }; 
  "ans"
}>.

Coercion to_loc : val >-> loc.

Lemma spmv_monolithic_spec `{Inhab D} (x_mval x_colind x_rowptr x_dvec : loc) : 
  {{ .arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     .arr(x_dvec, dvec)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) .arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) .arr(x_dvec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}                 => spmv_monolithic x_mval x_colind x_rowptr x_dvec];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, (\exists p, \exists vl : int -> binary64, 
    \[hv[`1]((0,0)) = val_loc p /\ forall i : int, 0 <= i < Nrow ->
      @feq Tdouble (vl i) (Sum_fma float_unit (lof id Ncol) (fun j => (to_float (hv[`2]((i, j))), dvec[j])))] \*
    harray_fun_float vl p Nrow (Lab (1,0) (0,0)))
      \* \Top }}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver).
  rewrite -!hbig_fset_hstar; match goal with
    |- context[?a \* ?b \* ?c \* ?d \* hbig_fset _ _ ?ff] =>
      pose (Inv (p : loc) (i : int) := a \* b \* c \* d \* (p ~⟨(1%Z, 0%Z), (0, 0)⟩~> rowptr[i])); pose (R := ff)
  end; rewrite -> ! hbig_fset_hstar.
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : (xwp; xapp (@htriple_allocf0_unary)=> // s; do 2 (xwp; xapp); move=> nxt)...
  rewrite prod_cascade.
  xfor_specialized_normal_float (Inv nxt) R R (fun hv i => (Sum_fma float_unit (lof id Ncol) (fun j => (to_float (hv[`2]((i, j))), dvec[j])))) (fun=> float_unit) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : (xwp; xapp=> tmp; do 4 (xwp; xapp))...
    xsubst (snd : _ -> int)...
    (* SV as subpart *)
    have Hl : length (colind_seg l0) = rowptr[l0 + 1] - rowptr[l0] :> int.
    1: rewrite /colind_seg list_interval_length...
    xfocus (2,0) (colind_seg l0).
    rewrite (hbig_fset_part (`[0, Ncol]) (colind_seg l0)).
    (* label has been distributed, so need to recover; otherwise it is hard to apply sv_float.get_spec_out *)
    replace (hbig_fset hstar (_ ∖ _) _) with (hbig_fset hstar ⟨(2, 0), `[0, Ncol] ∖ colind_seg l0⟩ 
      (fun d : labeled int => 
      harray_float mval x_mval d \*
      harray_int colind x_colind d \*
      harray_int rowptr x_rowptr d \*
      harray_float dvec x_dvec d)) by (rewrite hstar_fset_Lab; auto).
    rewrite -> ! hbig_fset_hstar with (fs:=⟨(2, 0), `[0, Ncol] ∖ colind_seg l0⟩).
    xapp sv_float.get_spec_out=> //...
    { case=> ?? /[! @indom_label_eq]-[_]/=; rewrite /intr filter_indom; autos*. }
    xin (1,0) : idtac.
    rewrite intr_list ?(fset_of_list_nodup 0) ?Hl ?Union_interval_change2 //; auto.
    2: intros x0 Hin; eapply colind_leq, in_interval_list; eauto.
    set (R2 (i : int) := arr(x_colind, colind)⟨2, i⟩ \* .arr(x_mval, mval)⟨2, i⟩ \* .arr(x_dvec, dvec)⟨2, i⟩).
    rewrite -> ! hbig_fset_hstar.
    match goal with
      |- context[?u1 \* ?u2 \* ?u3 \* ?u4 \* _ \* ?u6 \* ?u7 \* ?u8 \* (_ \* _ \* ?u9 \* _) \* ?u10 \* ?u11 \* ?u12] =>
        pose (Inv2' (i : int) := u1 \* u2 \* u3 \* u4 \* u9 \* u10 \* u11 \* u12);
        pose (Inv2 (i : int) := u6 \* u7 \* u8 \* Inv2' i)
    end.
    xfor_sum_fma Inv2 R2 R2 (fun hv i => (to_float (hv[`2](colind[i])), dvec[colind[i] ])) tmp.
    { rewrite /Inv2 /R2.
      xin (1,0) : xwp; xapp(@lhtriple_array_read_float); xwp; xapp(@lhtriple_array_read); xwp; xapp(@lhtriple_array_read_float). (* TODO why simply xapp does not work here? *)
      (xin (1,0): xapp (@fma.spec)=> y)... 
      xapp (@sv_float.get_spec_in)=> //; try math... xsimpl*.
      all: rewrite -list_interval_nth; try math...
      all: replace (_ + (l4 - _)) with l4 by math.
      1: split; by apply finite_suffcond. xsimpl*. }
    { intros Hneq Hi Hj Hq. apply Hneq. 
      enough (abs (i0 - rowptr[l0]) = abs (j0 - rowptr[l0]) :> nat) by math.
      eapply NoDup_nth. 4: apply Hq. all: try math; try assumption. by apply nodup_eachcol. }
    { rewrite /colind_seg -list_interval_nth; try f_equal; try math... }
    intros Hfin. simpl in Hfin. xwp; xapp... xwp; xapp.
    rewrite /Inv2'. xapp (@lhtriple_array_set_pre). 
    match goal with |- context[_ ~⟨(1%Z, 0%Z), 0⟩~> val_float ?aa] => xsimpl aa end.
    erewrite Sum_fma_eq; [ | move=> i0 ?; rewrite to_float_if pair_fst_If; reflexivity ].
    rewrite Sum_fma_filter_If -?sorted_bounded_sublist //; try solve [ intros; by apply finite_suffcond | idtac ].
    2: by apply sorted_eachcol. 2: intros x0 Hin; eapply colind_leq, in_interval_list; eauto.
    2:{ intros a0 _ (n & Hn & <-)%(In_nth _ _ 0). replace n with (abs n) by math. 
      rewrite -list_interval_nth; try math... apply Hfin; math. }
      rewrite -/(Sum_fma _ _ _) (Sum_fma_lof) /= Sum_fma_list_interval //=... }
    { apply Sum_fma_feq=>? /In_lof_id ? /=. split; auto. rewrite hvE //; autorewrite with indomE; simpl; split; auto; try math. }
    { xwp; xval. xsimpl*. }
Qed.

Ltac xapp_big E := 
  rewrite -> ! hbig_fset_hstar;
  xapp E=> //; rewrite -?hbig_fset_hstar.

Definition spmv' := 
  <{
  fun mval colind rowptr dvec =>
  let "ans" = allocf0 Nrow in
  let "row_ptr[0]" = read_array rowptr 0 in
  for i <- [0, Nrow] {
    let s = ref float_unit in
    let h = read_array rowptr i in
    let "i + 1" = i + 1 in
    let "row_ptr[i + 1]" = read_array rowptr "i + 1" in
    for j <- [h, "row_ptr[i + 1]"] {
      let x = mval[.j] in 
      let c = colind[j] in 
      let v = dvec[.c] in 
      fma.func s x v
    };
    let "res" = ! s in
    free s;
    val_array_set "ans" i "res"
  }; 
  "ans"
}>.

Hint Resolve lhtriple_array_set_pre : lhtriple.

Tactic Notation "seclocal_solver2" :=
  first [ rewrite /colind_seg list_interval_nth'; auto; solve [ math | seclocal_solver ]
    | rewrite /colind_seg list_interval_length; auto; solve [ math | seclocal_solver ]
    | rewrite /colind_seg -list_interval_nth; auto; solve [ math | seclocal_solver ]
    | idtac ]; auto.

Lemma spmv_spec' `{Inhab (labeled int)} `{Inhab D} (x_mval x_colind x_rowptr x_dvec : loc) : 
  {{ .arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     .arr(x_dvec, dvec)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) .arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) .arr(x_dvec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}                 => spmv' x_mval x_colind x_rowptr x_dvec];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, 
  harray_fun_float'  
    (fun i => (Sum_fma float_unit (lof id Ncol) (fun j => (to_float (hv[`2]((i, j))), dvec[j]))))
    (hv[`1]((0,0))) Nrow (Lab (1,0) (0,0)) \* \Top }}.
Proof with (try solve [ seclocal_solver | seclocal_solver2 | auto using finite_suffcond ]; seclocal_fold; try lia).
  xset_Inv Inv 1; xset_R Dom Inv R 2.
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : (xwp; xapp (@htriple_allocf0_unary)=> // s; xwp; xapp)...
  rewrite prod_cascade.
  xfor_specialized_normal_float' Inv R R (fun hv i => (Sum_fma float_unit (lof id Ncol) (fun j => (to_float (hv[`2]((i, j))), dvec[j])))) (fun=> float_unit) s.
  { xin (2,0) : rewrite wp_prod_single /=...
    xin (1,0) : (xwp; xapp=> tmp; do 3 (xwp; xapp))...
    xsubst (snd : _ -> int)...
    clear Inv R. xset_Inv Inv 1 tmp. xset_R int Inv R 2%Z.
    xfocus* (2,0) (colind_seg l0).
    xapp_big sv_float.get_spec_out... 1: case=>??; indomE; autos*.
    xin (1,0) : idtac.
    have Hl : length (colind_seg l0) = rowptr[l0 + 1] - rowptr[l0] :> int...
    rewrite intr_list ?(fset_of_list_nodup 0) ?Hl ?Union_interval_change2...
    rewrite -> ! hbig_fset_hstar; xclean_heap.
    xfor_sum_fma Inv R R (fun hv i => (to_float (hv[`2](colind[i])), dvec[colind[i] ])) tmp...
    { (xin (1,0): do 3 (xwp; xapp); xapp (@fma.spec)=> y)... 
      xapp (@sv_float.get_spec_in)=> //; try math... xsimpl*...
      rewrite list_interval_nth'... }
    { move=> ??? HH. eapply (proj1 (NoDup_nthZ _ _) (nodup_eachcol H1)) in HH... }
    move=> /= Hfin; xwp; xapp... xwp; xapp; xapp; xsimpl.
    rewrite -/(Sum_fma _ _ _) Sum_fma_lof ?Sum_fma_filter_If'; try intro;
    rewrite -?sorted_bounded_sublist ?Sum_fma_list_interval ?In_lof_id //...
    move: (indexG0 a0 (colind_seg l0)); rewrite /Sum.mem=> ??.
    move=> /[dup] /(nth_index 0){2}<-; rewrite -index_mem=> ?.
    rewrite -list_interval_nth; try apply/(Hfin _ _).1... }
  { apply Sum_fma_feq=>? /In_lof_id ? /= /[! hvE]; indomE... }
  xwp; xval. xsimpl*.
Qed.

End spmv_monolithic.

(*
Context (yind yval : list int).
Context (M : int).
Hypothesis len_xind : length yind = M :> int.
Hypothesis len_xval : length yval = M :> int.
Hypothesis stored_yind : sorted yind.
Hypothesis yind_leq : forall x, In x yind -> 0 <= x < Ncol.
Hypothesis Nrow0 : Nrow > 0. (* we get rid of it later *)


Hypothesis sorted_eachcol : forall x : int, 0 <= x < Nrow -> sorted (colind_seg x).

Definition spmspv x_colind y_ind x_mval y_val := 
  let dot := sv.sv_dotprod x_colind y_ind x_mval y_val in
  <{
  fun rowptr =>
  let s = alloc0 Nrow in
  for i <- [0, Nrow] {
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
    let x = dot lb rb 0 M in 
      val_array_set s i x
  }; 
  s
}>.

Arguments Union_same {_ _} _ _.

Lemma spmspv_spec `{Inhab D}
  (x_mval x_colind x_rowptr y_ind y_val : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     arr(y_ind, yind)⟨1, (0,0)⟩ \* 
     arr(y_val, yval)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `[0, Ncol]) arr(y_ind, yind)⟨3, (0,i)⟩) \* 
     (\*_(i <- `[0, Ncol]) arr(y_val, yval)⟨3, (0,i)⟩) }}
  [{
    {1| ld in `{(0,0)}                 => spmspv x_colind y_ind x_mval y_val x_rowptr};
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_colind x_rowptr ld.1 ld.2};
    {3| ld in `{0}       \x `[0, Ncol] => sv.get ld.2 y_ind y_val 0 M}
  }]
  {{ hv, (\exists p, 
    \[hv[`1]((0,0)) = val_loc p] \*
    harray_fun (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * hv[`3]((0, j))) p Nrow (Lab (1,0) (0,0)))
      \* \Top }}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver; try lia).
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : (xwp; xapp (@htriple_alloc0_unary)=> // s)...
  rewrite prod_cascade -(Union_same Nrow (`{0} \x `[0, Ncol])) //.
  set (R1 (i : Dom) := arr(x_mval, mval)⟨2, i⟩ \*
    arr(x_colind, colind)⟨2, i⟩ \* 
    arr(x_rowptr, rowptr)⟨2, i⟩).
  set (R2 (i : Dom) := arr(y_ind, yind)⟨3, i⟩ \*
    arr(y_val, yval)⟨3, i⟩).
  set (Inv (i : int) := arr(x_mval, mval)⟨1, (0,0)⟩ \* 
    arr(x_colind, colind)⟨1, (0,0)⟩ \* 
    arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
    arr(y_ind, yind)⟨1, (0,0)⟩ \* 
    arr(y_val, yval)⟨1, (0,0)⟩).
  xfor_specialized_normal2 Inv R1 R1 R2 R2 
    (fun hv i => Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * hv[`3]((0, j.2))))
    (fun=> 0) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xframe2 (arr(x_rowptr, rowptr)⟨1, (0, 0)⟩).
    xsubst (snd : _ -> int).
    xnapp @sv.sv_dotprod_spec... 
    { by rewrite -len_xind /slice slice_fullE. }
    { move=> ? /in_interval_list... }
    { move=> ?; rewrite -len_xind /slice slice_fullE... }
    move=> ?; rewrite -wp_equiv. xsimpl=>->.
    xapp @lhtriple_array_set_pre; try math.
    rewrite sum_prod1E; xsimpl. }
  { rewrite Union_same //; xsimpl*. }
  xwp; xval. xsimpl*. xsimpl; rewrite sum_prod1E; xsimpl.
Qed.
*)
End csr.

End csr.
