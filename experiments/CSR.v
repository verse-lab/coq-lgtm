Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl LibArray LibLoops Subst NTriple.
From LGTM.lib.theory Require Import LibListExt.
From LGTM.experiments Require Import Prelude UnaryCommon SV.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Module csr.

Import sv.

Section csr.

Notation "'mval'" := ("m_val":var) (in custom trm at level 0) : trm_scope.
Notation "'mind'" := ("m_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'mcrd'" := ("m_crd":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
Notation "'lb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'rb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.
Notation "'i''" := ("i_'":var) (in custom trm at level 0) : trm_scope.

Import List Vars list_interval_notation.

Context (mval mind mcrd : list int).
Context (N Nrow Ncol : int).
Hypothesis Nrow_nonneg : 0 <= Nrow.
Hypothesis len_mval : length mval = N :> int.
Hypothesis len_mind : length mind = N :> int.
Hypothesis len_mcrd : length mcrd = Nrow + 1 :> int.
Hypothesis mind_leq : forall x, In x mind -> 0 <= x < Ncol.
Hypothesis mcrd_first : List.nth (abs 0) mcrd 0 = 0.
Hypothesis mcrd_last : List.nth (abs Nrow) mcrd 0 = N.
Hypothesis mcrd_weakly_sorted : forall (i j : int), 
  (0 <= i <= Nrow) -> 
  (0 <= j <= Nrow) -> 
  (i <= j) -> 
  (mcrd[i] <= mcrd[j]).

Definition mind_seg (row : int) := mind [[ (mcrd[row]) -- (mcrd[row + 1]) ]].

Hypothesis nodup_eachcol : forall x : int, 0 <= x < Nrow -> NoDup (mind_seg x).

Tactic Notation "seclocal_solver" :=
  first [ assumption 
    | rewrite -/(mind_seg _); now apply nodup_eachcol
    | (* for mcrd[?] <= N *)
      try rewrite -> len_mind; try rewrite -> len_mval; 
      try rewrite <- mcrd_last; apply mcrd_weakly_sorted; math
    | (* for 0 <= mcrd[?] *)
      rewrite <- mcrd_first at 1; apply mcrd_weakly_sorted; math
    | (* for 0 <= mcrd[i] <= mcrd[i + 1] *)
      split; [ rewrite <- mcrd_first at 1 | ]; apply mcrd_weakly_sorted; math
    | intros; eapply mind_leq, in_interval_list; now eauto
    | idtac ]; auto.

(* Accessor function for CSR format. Similar to uCSR but encodings of each row are stored 
  consecutively in the natural order *)
Definition get := 
<{
  fun mval mind mcrd i j =>
    let lb = mcrd[i] in
    let i' = i + 1 in
    let rb = mcrd[i'] in
      sv.get j mind mval lb rb
}>.

(* #5 from the table
  Summation of all elements in sparse CSR matrix *)
Definition sum := 
  <{
  fun mval mind mcrd =>
  let s = ref 0 in
  for i <- [0, Nrow] {
    let lb = mcrd[i] in
    let i' = i + 1 in
    let rb = mcrd[i'] in
    let x = sv.sum mind mval lb rb in 
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


(* Specification for `sum` *)
Lemma sum_spec `{Inhab D} (m_val m_ind m_crd : loc) : 
  {{ arr(m_val, mval)⟨1, (0,0)⟩ \*
     arr(m_ind, mind)⟨1, (0,0)⟩ \*
     arr(m_crd, mcrd)⟨1, (0,0)⟩ \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_val, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_ind, mind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_crd, mcrd)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}   => sum m_val m_ind m_crd];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get m_val m_ind m_crd ld.1 ld.2}
  }]
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) hv[`2](i)] \* \Top}}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R Dom Inv R 2.
  xin 2 : xgo.
  xin 1 : xstep=> s...
  rewrite prod_cascade.
  xfor_sum Inv R R (fun hv i => Σ_(j <- `{i} \x `[0, Ncol]) hv[`2](j)) s.
  { xin 2 : rewrite wp_prod_single /=.
    xin 1 : do 3 xtep...
    xsubst (snd : _ -> int).
    xnapp sv.sum_spec...
    xsimpl=>->. xapp @incr.spec; rewrite sum_prod1E; xsimpl. }
  { xapp. xsimpl*. rewrite SumCascade //; disjointE. }
Qed.

Context (dvec : list int).
Context (dvec_len : length dvec = Ncol :> int).


(* #6 from the table
  Dot product of a sparse CSR matrix and a dense vector *)
Definition spmv := 
  <{
  fun mval mind mcrd dvec =>
  let s = alloc0 Nrow in
  for i <- [0, Nrow] {
    let lb = mcrd[i] in
    let i' = i + 1 in
    let rb = mcrd[i'] in
    let x = sv.dotprod mind mval dvec lb rb in 
    s[i] := x
  }; 
  s
}>.

(* Specification for `spmv` *)
Lemma spmv_spec `{Inhab D} (m_val m_ind m_crd x_dvec : loc) : 
  {{ arr(m_val, mval)⟨1, (0,0)⟩ \*
     arr(m_ind, mind)⟨1, (0,0)⟩ \*
     arr(m_crd, mcrd)⟨1, (0,0)⟩ \*
     arr(x_dvec, dvec)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_val, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_ind, mind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_crd, mcrd)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_dvec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}                 => spmv m_val m_ind m_crd x_dvec];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get m_val m_ind m_crd ld.1 ld.2}
  }]
  {{ hv, 
    harray_fun_int (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * dvec[j]) (hv[`1]((0,0))) Nrow (Lab (1,0) (0,0))
      \* \Top }}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R Dom Inv R 2.
  xin 2 : xgo.
  xin 1 : (xwp; xapp (@htriple_alloc0_unary)=> // s)...
  rewrite prod_cascade.
  xfor_arrayset Inv R R (fun hv (i : int) => Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * dvec[j.2])) (fun _ : int => 0) s.
  { xin 2 : rewrite wp_prod_single /=.
    xin 1 : xgo...
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


Hypothesis sorted_eachcol : forall x : int, 0 <= x < Nrow -> sorted (mind_seg x).

(* #7 from the table
  Product of sparse CSR matrix and sparse SV vector *)
Definition spmspv m_ind y_ind m_val y_val := 
  let dot := sv.sv_dotprod m_ind y_ind m_val y_val in
  <{
  fun mcrd =>
  let s = alloc0 Nrow in
  for i <- [0, Nrow] {
    let lb = mcrd[i] in
    let i' = i + 1 in
    let rb = mcrd[i'] in
    let x = dot lb rb 0 M in 
      s[i] := x
  }; 
  s
}>.

(* Specification for `spmspv` *)
Lemma spmspv_spec `{Inhab D}
  (m_val m_ind m_crd y_ind y_val : loc) : 
  {{ arr(m_val, mval)⟨1, (0,0)⟩ \*
     arr(m_ind, mind)⟨1, (0,0)⟩ \*
     arr(m_crd, mcrd)⟨1, (0,0)⟩ \*
     arr(y_ind, yind)⟨1, (0,0)⟩ \* 
     arr(y_val, yval)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_val, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_ind, mind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_crd, mcrd)⟨2, i⟩) \*
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_ind, yind)⟨3, i⟩) \* 
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    {1| ld in `{(0,0)}                 => spmspv m_ind y_ind m_val y_val m_crd};
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get m_val m_ind m_crd ld.1 ld.2};
    {3| ld in `{0}       \x `[0, Ncol] => sv.get ld.2 y_ind y_val 0 M}
  }]
  {{ hv,
    harray_fun_int (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * hv[`3]((0, j))) (hv[`1]((0,0))) Nrow (Lab (1,0) (0,0))
      \* \Top }}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver; try lia).
  xset_Inv Inv 1; xset_R_core Dom R1 2; xset_R_core Dom R2 3. xset_clean R1 R2 Inv.
  xin 2 : xgo.
  xin 1 : (xwp; xapp (@htriple_alloc0_unary)=> // s)...
  rewrite prod_cascade -(Union_same Nrow (`{0} \x `[0, Ncol])) //; try math.
  xfor_arrayset Inv R1 R1 R2 R2 
    (fun hv (i : int) => Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * hv[`3]((0, j.2)))) (fun _ : int => 0) s.
  { xin 2 : rewrite wp_prod_single /=.
    xin 1 : xgo...
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
