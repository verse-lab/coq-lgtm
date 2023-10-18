Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct Unary_IndexWithBounds Loops SV2.
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

Lemma csrij_spec_in `{Inhab D} (x_mval x_colind x_rowptr : loc) (i j : int) d : 
  htriple (single d tt) 
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

Lemma csrij_spec_out_unary `{Inhab D} (x_mval x_colind x_rowptr : loc) (i j : int) d :
  htriple (single d tt) 
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
Lemma csrij_spec_out `{Inhab D} fs (x_mval x_colind x_rowptr : loc) : 
  htriple fs
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
  xapp csrij_spec_out_unary=> //= ??->.
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
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) hv[`2](i)] \* \Top}}.
Proof with (try seclocal_fold; seclocal_solver).
  xin (1,0) : xwp; xapp=> s...
  xin (2,0) : do 3 (xwp; xapp).
  (* TODO extract this to be a lemma *)
  assert (`[0, Nrow] \x `[0, Ncol] = Union `[0, Nrow] (fun i => `{i} \x `[0, Ncol])) as E.
  { apply fset_extens. intros (r, c).
    rewrite indom_prod indom_Union !indom_interval /=.
    split.
    { intros (Hr & Hc). exists r. 
      rewrite indom_prod !indom_interval indom_single_eq //=. }
    { intros (f & Hq). 
      rewrite indom_prod !indom_interval indom_single_eq /= in Hq. eqsolve. }
  }
  rewrite E.
  set (R i := 
    arr(x_mval, mval)⟨2, i⟩ \*
    arr(x_colind, colind)⟨2, i⟩ \* 
    arr(x_rowptr, rowptr)⟨2, i⟩).
  set (Inv (i : int) := 
    arr(x_mval, mval)⟨1, (0,0)⟩ \* 
    arr(x_colind, colind)⟨1, (0,0)⟩ \* 
    arr(x_rowptr, rowptr)⟨1, (0,0)⟩).
  xin (1,0) : idtac... (* making 1 be above 2 *)
  xfor_sum Inv R (fun=> \Top) (fun hv i => Σ_(j <- `{i} \x `[0, Ncol]) hv[`2](j)) s.
  { rewrite /Inv /R.
    xin (1,0) : do 3 (xwp; xapp)...
    xframe2 (arr(x_rowptr, rowptr)⟨1, (0, 0)⟩). xsimpl.
    xin (1,0) : idtac. (* format fix *)
    admit. (* how to use the spec of sv.sum here? *)
  }
  { intros Hneq Hi Hj. 
    apply disjoint_of_not_indom_both.
    intros (r, c). rewrite !indom_prod !indom_interval !indom_single_eq /=. math. }
  { xapp. xsimpl*. rewrite SumCascade; try reflexivity.
    (* repeating the proof above? *)
    intros i0 j0 Hneq. rewrite ! indom_interval=> ? ?.
    apply disjoint_of_not_indom_both.
    intros (r, c). rewrite !indom_prod !indom_interval !indom_single_eq /=. math. }
Abort.

End csr.

End csr.
