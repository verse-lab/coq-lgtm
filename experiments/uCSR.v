Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl LibArray LibLoops Subst NTriple.
From LGTM.lib.theory Require Import LibListExt.
From LGTM.experiments Require Import Prelude UnaryCommon SV.
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

Import List Vars list_interval_notation.

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

Context (yind yval : list int).
Context (M : int).
Hypothesis len_xind : length yind = M :> int.
Hypothesis len_xval : length yval = M :> int.
Hypothesis stored_yind : sorted yind.
Hypothesis yind_leq : forall x, In x yind -> 0 <= x < Ncol.
Hypothesis Nrow0 : Nidx > 0. (* we get rid of it later *)

Definition colind_seg (row : int) := colind [[ (rowptr[row]) -- (rowptr[row + 1]) ]].

Hypothesis nodup_eachcol : forall x : int, 0 <= x < Nidx -> NoDup (colind_seg x).
Hypotheses nodup_midx : NoDup midx.

Tactic Notation "seclocal_solver" :=
  try (rewrite index_nodup=> //; math);
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
    | intros; now case_if
    | move=> >; rewrite -len_xind slice_fullE //
    | lia
    | intros; apply midx_leq, nth_In; math
    | idtac ]; auto.

Definition indexf := index.func Nidx.

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
  xwp; xsimpl=> /(memNindex _)?; xapp @index.spec... 
  xstep; xwp; xif=> ?... 
  xwp; xval; xsimpl*.
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
Proof. by xpointwise_build (@get_spec_out_unary). Qed.

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

Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition eld := @LibWP.eld (int * int)%type.
Coercion eld : D >-> Dom.

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
  xfocus* 2 (indom (midx \x `[0, Ncol])).
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap.
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  xin 1 : xwp; xapp=> s...
  xfor_sum Inv R R (fun hv i => Σ_(j <- `{midx[i]} \x `[0, Ncol]) hv[`2](j)) s.
  { xin 2 : rewrite wp_prod_single /=.
    xin 1 : do 3 (xwp; xapp)...
    xsubst (snd : _ -> int).
    xfocus (2,0); rewrite -> ! hbig_fset_hstar.
    xwp; xapp (@index.Spec `[0, Ncol] Nidx (2,0) midx x_midx (fun=> midx[l0]))=> //.
    rewrite index_nodup //; try math.
    xwp; xapp. xwp; xif=> ?; [ | math ].
    do 3 (xwp; xapp).
    xunfocus; xin 1 : idtac. (* reformat *)
    xnapp sv.sum_spec...
    xsimpl=>->. xapp @incr.spec. rewrite sum_prod1E. xsimpl. }
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
  {{ hv,
    harray_fun_int (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * dvec[j]) (hv[`1]((0,0))) Nrow (Lab (1,0) (0,0))
      \* \Top }}.
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus* 2 (indom (midx \x `[0, Ncol])).
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap.
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  xin 1 : xmalloc ans...
  xfor_arrayset Inv R R 
    (fun hv (i : int) => (If (In i midx) then Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * dvec[j.2]) else 0)) 
    (fun _ : int => 0) ans midx...
  { xin* 2: xapp* @index.specs; xstep; xwp; xif=> [?|]; xgo...
    xin 1 : xgo...
    rewrite index_nodup //; try math.
    xsubst (snd : _ -> int).
    xnapp sv.dotprod_spec...
    xsimpl=>->; xapp; rewrite sum_prod1E; xsimpl.
    case: classicT=> [?|/(_ (nth_In _ _ _))] //; lia. }
  xwp; xval. xsimpl*. erewrite -> harray_fun_int_congr; try assumption; first xsimpl*.
  move=> i Hi /=. xsum_normalize.
  case_if.
  { rewrite sum_prod1E /=; apply SumEq=> >; indomE.
    case: classicT=> // /[swap]? []; exists (index i midx); indomE=> /=.
    splits; try tauto. 
    { rewrite -len_midx index_mem //; splits*; exact/(indexG0). }
    { by rewrite nth_index. } }
  { rewrite -> SumEq with (G:=fun=> 0)=> [|?]; first by rewrite Sum0s.
    indomE; case: classicT=> // -[?]; indomE=> /=-[?][*]. 
    case: C; subst; apply/nth_In; math. }
Qed.



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

Notation size := length.

(**************************************************************************************)
(*********  The full verison of the proof snippet from Section 4 of the paper *********)
(**************************************************************************************)
(* 
  Major differencies with the paper verison: 
  (1) Our Coq implementation only supports LGTM triples, where index sets of all 
    components have the same type. To run the `uscr_get` funtion (`get` here) we need an
    index set with elements of type `int * int`. That is why indexs sets of the first 
    and the third components are artifically made to have the same type as well. 
  (2) Instread `xfor` tactic from the paper, we use a more convinient tactic 
    `xfor_bigstr`. This tactic takes not the whole invariant as an input, but only that
    part of it, which changes within the inductive step. Here we provide it some
    technical arguments `Inv`, `R2`, `R3`, althother with two verisions of the changed 
    clause from I_for: before and after the induvtive step.
  (3) The Coq notation for `x(i) |-> y` heap predicate is `x |-(i)-> y`. 
  (4) The Coq notation for `arr(x(i), y)` heap predicate is `arr(x, y)⟨i⟩`. 
  (5) In the paper the output of each component is a separate hyper vaule. Here all 
    outputs are assembled in the same hyper value `hv`. To reference to the outcome of
    each particular componet with tag `t`, one should write `hv[`t]`.
*)

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
  {{ hv,
    arrf(hv[`1]((0,0)), i in Nrow => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * hv[`3]((0, j)))⟨1, (0,0)⟩
      \* \Top }}.
Proof with (try seclocal_fold; seclocal_solver; autos* ).
  xstart. (* proof start *)
  (* § 2.2 *)    
  xfocus* 2 (indom (midx \x `[0, Ncol])).
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap. (* clean up unused assertions *)
  (* § 2.1.1 *)
  xin 1: xmalloc p=> //; xret...
  (* frame out unused part of ans array *)
  xframe_array p midx...
  { move=> *; erewrite <-Sum0s at 1; apply/SumEq=> ?.
    indomE=> /=; case_if... }
  (* partition index set into Si to apply For-rule *)
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  rewrite -(Union_same Nidx (`{0} \x `[0, Ncol])) //; try math.
  (* § 2.3 *)
  xfor_bigstr Inv R2 R3
    (fun l => p .+ midx[l] |-(1, (0, 0))-> 0)
    (fun l hv => p .+ midx[l] |-(1, (0, 0))->
      Σ_(j <- `[0, Ncol]) hv[`2]((midx[l], j)) * hv[`3]((0, j))).
  { xin* 2: xapp* @index.specs; xstep; xwp; xif=> [?|]; xgo...
    xin 1: xgo...
    rewrite index_nodup... (* simplify goal *)
    (* § 2.4 *)
    xsubst (snd : _ -> int).
    (* § 2.5 *)
    xnapp sv.sv_dotprod_spec... 
    xsimpl=>->; xapp; xsimpl. (* store result of spvspv *) }
  (* solve arithmetic to adjust big summations in precondition *)
  erewrite hbig_fset_eq with (fs := `[0, Nidx]); first xsimpl*.
  move=> ?; indomE=> ?; do 2? f_equal; apply/SumEq=> ?.
  rewrite -prod_Union_distr -len_midx -fset_of_list_nodup; indomE=> //=.
  rewrite -index_mem index_nodup; try case_if...
Qed. 

End unordered_csr.

End unordered_csr.
