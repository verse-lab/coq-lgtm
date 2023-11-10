Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl Struct Loops Subst NTriple.
From LGTM.lib.theory Require Import LibListExt.
From LGTM.experiments Require Import Prelude Unary SV.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Module csr.

Import sv.

Section csr.

Notation "'mval'" := ("m_val":var) (in custom trm at level 0) : trm_scope.
Notation "'colind'" := ("col_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'rowptr'" := ("row_ptr":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
Notation "'lb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'rb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.
Notation "'i''" := ("i_'":var) (in custom trm at level 0) : trm_scope.

Import List Vars list_interval_notation.

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
  (rowptr[i] <= rowptr[j]).

Definition colind_seg (row : int) := colind [[ (rowptr[row]) -- (rowptr[row + 1]) ]].

Hypothesis nodup_eachcol : forall x : int, 0 <= x < Nrow -> NoDup (colind_seg x).

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
    | intros; eapply colind_leq, in_interval_list; now eauto
    | idtac ]; auto.

Definition get := 
<{
  fun mval colind rowptr i j =>
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
      sv.get j colind mval lb rb
}>.

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

Tactic Notation "seclocal_fold" := 
  rewrite ?label_single ?wp_single
    -?/(harray_int _ _ _)
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition eld := @LibWP.eld (int * int)%type.
Coercion eld : D >-> Dom.

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
  xset_Inv Inv 1; xset_R Dom Inv R 2.
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : xwp; xapp=> s...
  rewrite prod_cascade.
  xfor_sum Inv R R (fun hv i => Σ_(j <- `{i} \x `[0, Ncol]) hv[`2](j)) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xsubst (snd : _ -> int).
    xnapp sv.sum_spec...
    xsimpl=>->. xapp @incr.spec; rewrite sum_prod1E; xsimpl. }
  { xapp. xsimpl*. rewrite SumCascade //; disjointE. }
Qed.

Context (dvec : list int).
Context (dvec_len : length dvec = Ncol :> int).

Definition spmv := 
  <{
  fun mval colind rowptr dvec =>
  let s = alloc0 Nrow in
  for i <- [0, Nrow] {
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
    let x = sv.dotprod colind mval dvec lb rb in 
    val_array_set s i x
  }; 
  s
}>.

Lemma spmv_spec `{Inhab D} (x_mval x_colind x_rowptr x_dvec : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     arr(x_dvec, dvec)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_dvec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}                 => spmv x_mval x_colind x_rowptr x_dvec];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, (\exists p, 
    \[hv[`1]((0,0)) = val_loc p] \*
    harray_fun_int (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * dvec[j]) p Nrow (Lab (1,0) (0,0)))
      \* \Top }}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R Dom Inv R 2.
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : (xwp; xapp (@htriple_alloc0_unary)=> // s)...
  rewrite prod_cascade.
  xfor_arrayset Inv R R (fun hv (i : int) => Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * dvec[j.2])) (fun _ : int => 0) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xsubst (snd : _ -> int).
    xnapp sv.dotprod_spec...
    xsimpl=>->. xapp @lhtriple_array_set_pre; try math.
    rewrite sum_prod1E; xsimpl. }
  { xwp; xval. xsimpl*. xsimpl; rewrite sum_prod1E; xsimpl. }
Qed.

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
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_ind, yind)⟨3, i⟩) \* 
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    {1| ld in `{(0,0)}                 => spmspv x_colind y_ind x_mval y_val x_rowptr};
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_colind x_rowptr ld.1 ld.2};
    {3| ld in `{0}       \x `[0, Ncol] => sv.get ld.2 y_ind y_val 0 M}
  }]
  {{ hv, (\exists p, 
    \[hv[`1]((0,0)) = val_loc p] \*
    harray_fun_int (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * hv[`3]((0, j))) p Nrow (Lab (1,0) (0,0)))
      \* \Top }}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver; try lia).
  xset_Inv Inv 1; xset_R_core Dom R1 2; xset_R_core Dom R2 3. xset_clean R1 R2 Inv.
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : (xwp; xapp (@htriple_alloc0_unary)=> // s)...
  rewrite prod_cascade -(Union_same Nrow (`{0} \x `[0, Ncol])) //; try math.
  xfor_arrayset Inv R1 R1 R2 R2 
    (fun hv (i : int) => Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * hv[`3]((0, j.2)))) (fun _ : int => 0) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xsubst (snd : _ -> int).
    xnapp @sv.sv_dotprod_spec... 
    { by rewrite -len_xind slice_fullE. }
    { move=> ?; rewrite -len_xind slice_fullE... }
    xsimpl=>->. xapp @lhtriple_array_set_pre; try math.
    rewrite sum_prod1E; xsimpl. }
  { rewrite Union_same //; try math; xsimpl*. xsimpl*. }
  xwp; xval. xsimpl*. xsimpl; rewrite sum_prod1E; xsimpl.
Qed.

End csr.

End csr.
