Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct Unary_IndexWithBounds Loops.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Definition to_int (v : val) : int := 
  match v with 
  | val_int i => i 
  | _ => 0
  end.

Coercion to_int : val >-> Z.

Module Export AD := WithUnary(Int2Dom).

Module csr.

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
      try rewrite -> len_colind; try rewrite <- rowptr_last; apply rowptr_weakly_sorted; math
    | (* for 0 <= rowptr[i] <= rowptr[i + 1] *)
      split; [ rewrite <- rowptr_first at 1 | ]; apply rowptr_weakly_sorted; math
    | idtac ]; auto.

Definition indexf := index_bounded.func.

Definition csrij := 
<{
  fun mval colind rowptr i j =>
    let "lb" = read_array rowptr i in
    let "ii" = i + 1 in
    let "rb" = read_array rowptr "ii" in
    let k = indexf "lb" "rb" j colind in
    let c = k < "rb" in
    if c
    then 
      let "tmp" = read_array mval k in "tmp"
    else 0
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
  xwp; xapp index_bounded.spec=> //...
  rewrite /colind_seg index_nodup...
  2: rewrite list_interval_length...
  xwp; xapp. xwp; xif=> ?; try math. 
  xwp; xapp. xwp; xval. xsimpl*.
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
  rewrite -wp_equiv; xsimpl.
  intros (? & HH%memNindex). 
  do 3 (xwp; xapp).
  xwp; xapp index_bounded.spec=> //...
  rewrite -/(colind_seg _) HH list_interval_length...
  xwp; xapp. xwp; xif=> ?; try math. xwp; xval. xsimpl*.
Qed.

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
  fun mval =>
  let s = ref 0 in
  for i <- [0, N] {
    let x = mval[i] in 
    s += x
  };
  ! s
}>.

Tactic Notation "seclocal_fold" := 
  rewrite ?label_single ?wp_single
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Lemma Union_depprod_collapse : 

Lemma csrsum_spec `{Inhab D} (x_mval x_colind x_rowptr : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}   => csrsum x_mval];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => csrij x_mval x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) hv[`2](i)] \* \Top}}.
Proof with (try seclocal_fold; seclocal_solver).
  set (is_valid_coor := (fun rc : int * int => 0 <= rc.1 < Nrow /\ In rc.2 (colind_seg rc.1))).
  xfocus (2,0) is_valid_coor.
  rewrite (hbig_fset_part (`[0, Nrow] \x `[0, Ncol]) is_valid_coor). (* TODO: there is a todo in COO here *)
  xapp csrij_spec_out=> //.
  { case=> ?? /[! @indom_label_eq]-[_]/=. 
    rewrite /is_valid_coor /intr filter_indom indom_prod indom_interval; autos*. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); 
  set (H2 := hbig_fset hstar (_ ∖ _) _);
  set (H3 := hbig_fset hstar (_ ∖ _) _).
  xframe (H1 \* H2 \* H3); clear H1 H2 H3.
  (* TODO this is not a good proof, though; a more natural way is to split the For loop? *)
  (* TODO need some segmentation *)
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ is_valid_coor = 
    Union (interval 0 Nrow) (fun i => Union (interval (nth (abs i) rowptr 0) (nth (abs (i + 1)) rowptr 0)) 
      (fun j => single (i, nth (abs j) colind 0) tt)).
  { subst is_valid_coor. apply fset_extens. intros (r, c).
    rewrite /intr /colind_seg filter_indom indom_prod indom_Union ?indom_interval //=.
    split.
    { intros ((Hr & Hc) & _ & Hin).
      exists r.
      rewrite indom_interval. split; auto. 
      rewrite indom_Union.
      pose proof Hin as Hin'%(nth_index 0).
      rewrite <- index_mem, -> list_interval_length in Hin...
      set (idx := index _ _) in Hin, Hin'.
      assert (0 <= idx) by (subst idx; apply indexG0).
      exists ((nth (abs r) rowptr 0) + idx).
      rewrite indom_interval indom_single_eq. 
      rewrite -> list_interval_nth with (lb:=(nth (abs r) rowptr 0)) (rb:=(nth (abs (r + 1)) rowptr 0))...
      rewrite Hin'. split; try math; auto. }
    { intros (r' & Hr' & HH).
      rewrite indom_Union in HH. destruct HH as (c' & Hc' & HH).
      rewrite -> indom_interval in Hr', Hc'. rewrite indom_single_eq in HH.
      injection HH as <-. subst c.
      admit.
    }
  }
  rewrite E.


      assert (0 <= (nth (abs r') rowptr 0) <= (nth (abs (r' + 1)) rowptr 0)) as HH1...
      assert ((nth (abs (r' + 1)) rowptr 0) <= N) as HH2...
      assert (abs c' < Datatypes.length colind)%nat as HH3 by math.
      apply nth_In with (d:=0) in HH3.
      
      nth In


       

      
      
      


    simpl.
    setoid_rewrite indom_interval.
    setoid_rewrite indom_Union.
    setoid_rewrite indom_interval.
    setoid_rewrite indom_single_eq.
    

  xin (1,0) : xwp; xapp=> s...
  set (R i := 
    arr(x_mval, mval)⟨2, i⟩ \*
    arr(x_colind, colind)⟨2, i⟩ \* 
    arr(x_rowptr, rowptr)⟨2, i⟩).
  set (Inv (i : int) := 
    arr(x_mval, mval)⟨1, (0,0)⟩ \* 
    arr(x_colind, colind)⟨1, (0,0)⟩ \* 
    arr(x_rowptr, rowptr)⟨1, (0,0)⟩).

    For
  xfor_sum Inv R (fun=> \Top) (fun hv i => hv[`2]((xrow[i], xcol[i]))) s.
  xfor_big_op_lemma

  
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ is_valid_coor = is_valid_coor.

  

  xin (1,0) : xwp; xapp=> s...
  { apply/fset_extens=> -[??]. 
    rewrite /intr filter_indom indom_prod -fset_of_list_in; splits*.
    rewrite /Sum.mem in_combineE /= ?indom_interval=> -[]; autos*. }
  rewrite ?E (fset_of_list_nodup (0,0)) // lE.
  set (R i := 
    arr(x_row, xrow)⟨2, i⟩ \*
    arr(x_col, xcol)⟨2, i⟩ \* 
    arr(x_val, xval)⟨2, i⟩).
  set (Inv (i : int) := 
    arr(x_row, xrow)⟨1, (0,0)⟩ \* 
    arr(x_col, xcol)⟨1, (0,0)⟩ \* 
    arr(x_val, xval)⟨1, (0,0)⟩).
  xfor_sum Inv R (fun=> \Top) (fun hv i => hv[`2]((xrow[i], xcol[i]))) s.
  { rewrite /Inv /R.
    (xin (1,0): (xwp; xapp; xapp incr.spec=> y))...
    rewrite ?combine_nth /=; try lia.
    xapp get_spec_in=> //; xsimpl*. }
  { move=> Neq ???; apply/Neq. 
    move/NoDup_nthZ: nodup_xrowcol; apply; autos*; math. }
  { rewrite combine_nth //; lia. }
  { lia. }
  xapp; xsimpl.
  under (@SumEq _ _ _ (`[0, Nrow] \x `[0, Ncol])).
  { move=>*; rewrite to_int_if; over. }
  rewrite SumIf E (SumList (0,0)) // lE Sum0s.
  under (@SumEq _ _ _ `[0,N]).
  { move=> ?; rewrite -combine_nth; last lia. over. }
  math.
Qed.



End csr.

End csr.
