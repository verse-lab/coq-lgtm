Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Unary_IndexWithBounds.
From SLF Require Import Struct Loops SV Subst NTriple Loops2 Struct2 CSR ListCommon.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Module unordered_csr.

Import sv.

Section unordered_csr.

Notation "'mval'" := ("m_val":var) (in custom trm at level 0) : trm_scope.
Notation "'midx'" := ("m_idx":var) (in custom trm at level 0) : trm_scope.
Notation "'colind'" := ("col_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'rowptr'" := ("row_ptr":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
Notation "'lb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'rb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.
Notation "'i''" := ("i_'":var) (in custom trm at level 0) : trm_scope.

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Import List Vars.

Context (mval midx colind rowptr : list int).
Context (N Nrow Ncol Nidx : int).
Hypothesis Nrow_nonneg : 0 <= Nrow.
Hypothesis len_mval : length mval = N :> int.
Hypothesis len_midx : length midx = Nidx :> int.
Hypotheses Nidx_leq_Nrow : Nidx <= Nrow.
Hypothesis len_colind : length colind = N :> int.
Hypothesis len_rowptr : length rowptr = Nidx + 1 :> int.
Hypothesis colind_leq : forall x, In x colind -> 0 <= x < Ncol.
Hypothesis midx_leq : forall x, In x midx -> 0 <= x < Nrow.
Hypothesis rowptr_first : rowptr[0] = 0.
Hypothesis rowptr_last : rowptr[Nidx] = N.
Hypothesis rowptr_weakly_sorted : forall (i j : int), 
  (0 <= i <= Nidx) -> 
  (0 <= j <= Nidx) -> 
  (i <= j) -> 
  (rowptr[i] <= rowptr[j]).

Definition colind_seg (row : int) :=
  list_interval (abs rowptr[row]) (abs rowptr[row+1]) colind.

Hypothesis nodup_eachcol : forall x : int, 0 <= x < Nidx -> NoDup (colind_seg x).
Hypotheses nodup_midx : NoDup midx.

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
    | intros; eapply colind_leq, in_interval_list; now eauto
    | idtac ]; auto.

Definition indexf := Unary.index.func Nidx.

Definition get (x_mval : loc) := 
<{
  fun midx colind rowptr i j =>
      let i = indexf i midx in
      let "i < Nidx" = i < Nidx in
      if "i < Nidx" then
        let lb = read_array rowptr i in
        let i' = i + 1 in
        let rb = read_array rowptr i' in
          sv.get j colind x_mval lb rb
      else 0
}>.

Lemma get_spec_out_unary {D : Type} `{Inhab D} (x_midx x_mval x_colind x_rowptr : loc) (i j : int) d :
  @htriple D (single d tt) 
    (fun=> get x_mval x_midx x_colind x_rowptr i j)
    (\[~ In i midx] \*
      harray_int mval x_mval d \* 
      harray_int midx x_midx d \* 
      harray_int colind x_colind d \* 
      harray_int rowptr x_rowptr d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      harray_int mval x_mval d \* 
      harray_int midx x_midx d \* 
      harray_int colind x_colind d \* 
      harray_int rowptr x_rowptr d).
Proof with seclocal_solver.
  rewrite -wp_equiv; xsimpl=> Hnotin.
  apply memNindex in Hnotin.
  xwp; xapp @Unary.index.spec... xwp; xapp.
  xwp; xif=> HQ; try math.
  xwp; xval. xsimpl*.
Qed.

Lemma get_spec_out `{Inhab (labeled (int * int))} fs (x_midx x_mval x_colind x_rowptr : loc) : 
  @htriple (labeled (int * int)) fs
    (fun d => get x_mval x_midx x_colind x_rowptr (eld d).1 (eld d).2)
    (\[forall d, indom fs d -> ~ In (eld d).1 midx] \*
      (\*_(d <- fs) harray_int mval x_mval d) \* 
      (\*_(d <- fs) harray_int midx x_midx d) \* 
      (\*_(d <- fs) harray_int colind x_colind d) \* 
       \*_(d <- fs) harray_int rowptr x_rowptr d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      (\*_(d <- fs) harray_int mval x_mval d) \*
      (\*_(d <- fs) harray_int midx x_midx d) \* 
      (\*_(d <- fs) harray_int colind x_colind d) \*  
       \*_(d <- fs) harray_int rowptr x_rowptr d).
Proof.
  apply/htriple_val_eq/htriple_conseq;
  [|eauto|move=> ?]; rewrite -hstar_fset_pure -?hbig_fset_hstar; first last.
  { move=> ?; apply: applys_eq_init; reflexivity. }
  apply/htriple_union_pointwise=> [> -> //|[?][??]?]. 
  rewrite -wp_equiv wp_single /=. 
  xapp (@get_spec_out_unary)=> //= ??->.
  xsimpl*.
Qed.

Definition sum := 
  <{
    fun mval midx colind rowptr =>
    let s = ref 0 in
    for i <- [0, Nidx] {
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
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Arguments in_interval_list {_ _ _ _ _}.

Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition eld := @LibWP.eld (int * int)%type.
Coercion eld : D >-> Dom.

(* although this can be put in LibSepFmap.v, it depends on Sum.mem so put it here now *)
Fact prod_intr_list_on_1 {A B : Type} (fs1 : fset A) (fs2 : fset B) (la : list A) :
  (fs1 ∩ la) \x fs2 = (fs1 \x fs2) ∩ (indom (la \x fs2)).
Proof.
  apply fset_extens. intros (a, b).
  rewrite /intr !indom_prod !filter_indom !indom_prod /Sum.mem -fset_of_list_in /=. intuition.
Qed.

Hint Rewrite @filter_indom @indom_Union : indomE.
Hint Rewrite <- @fset_of_list_in :  indomE.


Lemma sum_spec `{Inhab D} `{Inhab (labeled int)} (x_mval x_colind x_rowptr x_midx : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_midx, midx)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_midx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}   => sum x_mval x_midx x_colind x_rowptr];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_midx x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) hv[`2](i)] \* \Top}}.
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus* (2,0) (indom (midx \x `[0, Ncol])).
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap.
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  xin (1,0) : xwp; xapp=> s...
  xfor_sum Inv R R (fun hv i => Σ_(j <- `{midx[i]} \x `[0, Ncol]) hv[`2](j)) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xsubst (snd : _ -> int).
    xfocus (2,0); rewrite -> ! hbig_fset_hstar.
    xwp; xapp (@Unary.index.Spec `[0, Ncol] Nidx (2,0) midx x_midx (fun=> midx[l0]))=> //.
    rewrite index_nodup //; try math.
    xwp; xapp. xwp; xif=> ?; [ | math ].
    do 3 (xwp; xapp).
    xunfocus; xin (1,0) : idtac. (* reformat *)
    xnapp sv.sum_spec...
    xsimpl=>->. xapp @incr.spec. rewrite csr.sum_prod1E. xsimpl. }
  { move=>Ha Hb Hc; left. move: Ha; apply contrapose, NoDup_nthZ; autos*; math. }
  xwp; xapp. xsimpl*. xsum_normalize.
  rewrite SumCascade -?prod_Union_distr -?len_midx -?(fset_of_list_nodup 0) ?E //.
  disjointE.
  move=>Ha Hb Hc; left. move: Ha; apply contrapose, NoDup_nthZ; autos*; math.
Qed.

Context (dvec : list int).
Context (dvec_len : length dvec = Ncol :> int).

(* challenge: unordered array set *)
Definition spmv := 
  <{
  fun mval midx colind rowptr dvec =>
  let s = alloc0 Nrow in
  for i <- [0, Nidx] {
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
    let i = read_array midx i in
    let x = sv.dotprod colind mval dvec lb rb in 
    val_array_set s i x
  }; 
  s
}>.

Lemma spmv_spec `{Inhab D} `{H__ : Inhab (labeled int)} (x_mval x_midx x_colind x_rowptr x_dvec : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_midx, midx)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     arr(x_dvec, dvec)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_midx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_dvec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}                 => spmv x_mval x_midx x_colind x_rowptr x_dvec];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_midx x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, (\exists p, 
    \[hv[`1]((0,0)) = val_loc p] \*
    harray_fun_int (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * dvec[j]) p Nrow (Lab (1,0) (0,0)))
      \* \Top }}.
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus* (2,0) (indom (midx \x `[0, Ncol])).
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap.
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  xin (1,0) : (xwp; xapp (@htriple_alloc0_unary)=> // s)...
  xfor_specialized Inv R R 
    (fun hv (i : int) => (If (In i midx) then Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * dvec[j.2]) else 0)) (fun=> 0) midx s.
  { intros. apply midx_leq, nth_In; math. }
  { case: classicT=> [?|/(_ (nth_In _ _ _))]; last lia.
    xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 4 (xwp; xapp)...
    xsubst (snd : _ -> int).
    xfocus (2,0); rewrite -> ! hbig_fset_hstar.
    xwp; xapp (@Unary.index.Spec `[0, Ncol] Nidx (2,0) midx x_midx (fun=> midx[l0]))=> //.
    rewrite index_nodup; try math; try assumption.
    xwp; xapp. xwp; xif=> ?; [ | math ].
    do 3 (xwp; xapp).
    xunfocus; xin (1,0) : idtac. (* reformat *)
    xnapp sv.dotprod_spec...
    xsimpl=>->. xapp @lhtriple_array_set_pre. rewrite csr.sum_prod1E. xsimpl. }
  { intros. now case_if. }
  xwp; xval. xsimpl*. erewrite -> harray_fun_int_congr; try assumption; first xsimpl*.
  move=> i Hi /=. xsum_normalize.
  case_if.
  { rewrite csr.sum_prod1E /=; apply SumEq=> >; indomE.
    case: classicT=> // /[swap]? []; exists (index i midx); indomE=> /=.
    splits; try tauto. 
    { rewrite -len_midx index_mem //; splits*; exact/(indexG0). }
    { by rewrite nth_index. } }
  { rewrite -> SumEq with (G:=fun=> 0)=> [|?]; first by rewrite Sum0s.
    indomE; case: classicT=> // -[?]; indomE=> /=-[?][*]. 
    case: C; subst; apply/nth_In; math. }
Qed.

Context (yind yval : list int).
Context (M : int).
Hypothesis len_xind : length yind = M :> int.
Hypothesis len_xval : length yval = M :> int.
Hypothesis stored_yind : sorted yind.
Hypothesis yind_leq : forall x, In x yind -> 0 <= x < Ncol.
Hypothesis Nrow0 : Nidx > 0. (* we get rid of it later *)


Hypothesis sorted_eachcol : forall x : int, 0 <= x < Nidx -> sorted (colind_seg x).

Definition spmspv x_colind y_ind x_mval y_val := 
  let dot := sv.sv_dotprod x_colind y_ind x_mval y_val in
  <{
  fun rowptr midx =>
  let s = alloc0 Nrow in
  for i <- [0, Nidx] {
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
    let i = read_array midx i in
    let x = dot lb rb 0 M in 
      val_array_set s i x
  }; 
  s
}>.

Lemma spmspv_spec `{Inhab D} `{H__ : Inhab (labeled int)}
  (x_mval x_colind x_midx x_rowptr y_ind y_val : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_midx, midx)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     arr(y_ind, yind)⟨1, (0,0)⟩ \* 
     arr(y_val, yval)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_midx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_ind, yind)⟨3, i⟩) \* 
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    {1| ld in `{(0,0)}                 => spmspv x_colind y_ind x_mval y_val x_rowptr x_midx};
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_midx x_colind x_rowptr ld.1 ld.2};
    {3| ld in `{0}       \x `[0, Ncol] => sv.get ld.2 y_ind y_val 0 M}
  }]
  {{ hv, (\exists p, 
    \[hv[`1]((0,0)) = val_loc p] \*
    harray_fun_int (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * hv[`3]((0, j))) p Nrow (Lab (1,0) (0,0)))
      \* \Top }}.
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R_core int R1 2; xset_R_core int R2 3. xset_clean Inv R1 R2.
  xfocus* (2,0) (indom (midx \x `[0, Ncol])).
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap.
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  rewrite -(Union_same (v:=Nidx) (`{0} \x `[0, Ncol])) //; try math.
  xin (1,0) : (xwp; xapp (@htriple_alloc0_unary)=> // s)...
  xfor_specialized2 Inv R1 R1 R2 R2 
    (fun hv (i : int) => (If (In i midx) then Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * hv[`3]((0,j.2))) else 0)) (fun=> 0) midx s.
  { intros. apply midx_leq, nth_In; math. }
  { case: classicT=> [?|/(_ (nth_In _ _ _))]; last lia.
    xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 4 (xwp; xapp)...
    xsubst (snd : _ -> int).
    xfocus (2,0); rewrite -> ! hbig_fset_hstar.
    xwp; xapp (@Unary.index.Spec `[0, Ncol] Nidx (2,0) midx x_midx (fun=> midx[l0]))=> //.
    rewrite index_nodup; try math; try assumption.
    xwp; xapp. xwp; xif=> ?; [ | math ].
    do 3 (xwp; xapp).
    xunfocus; xin (1,0) : idtac. (* reformat *)
    xnapp sv.sv_dotprod_spec...
    1-3: lia. 
    { by rewrite /slice -len_xind slice_fullE. }
    { move=> ?; rewrite /slice -len_xind slice_fullE... }
    xsimpl=>->. xapp @lhtriple_array_set_pre. rewrite csr.sum_prod1E. xsimpl. }
  { intros. now case_if. }
  { rewrite Union_same //; try math; xsimpl*. xsimpl*. }
  xwp; xval. xsimpl*. erewrite -> harray_fun_int_congr; try assumption; first xsimpl*.
  move=> i Hi /=. xsum_normalize.
  case_if.
  { rewrite csr.sum_prod1E /=; apply SumEq=> >; indomE.
    case: classicT=> // /[swap]? []; exists (index i midx); indomE=> /=.
    splits; try tauto. 
    { rewrite -len_midx index_mem //; splits*; exact/(indexG0). }
    { by rewrite nth_index. } }
  { rewrite -> SumEq with (G:=fun=> 0)=> [|?]; first by rewrite Sum0s.
    indomE; case: classicT=> // -[?]; indomE=> /=-[?][*]. 
    case: C; subst; apply/nth_In; math. }
Qed. 

End unordered_csr.

End unordered_csr.
