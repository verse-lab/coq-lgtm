Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibHypHeap LibWP LibXWP LibSepSimpl LibArray LibLoops Subst NTriple.
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
Notation "'mind'" := ("m_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'mcrd'" := ("m_crd":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
Notation "'lb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'rb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.
Notation "'i''" := ("i_'":var) (in custom trm at level 0) : trm_scope.

Import List Vars list_interval_notation.

Context (mval midx mind mcrd : list int).
Context (N Nrow Ncol Nidx : int).
Hypothesis Nrow_nonneg : 0 <= Nrow.
Hypothesis len_mval : length mval = N :> int.
Hypothesis len_midx : length midx = Nidx :> int.
Hypotheses Nidx_leq_Nrow : Nidx <= Nrow.
Hypothesis len_mind : length mind = N :> int.
Hypothesis len_mcrd : length mcrd = Nidx + 1 :> int.
Hypothesis mind_leq : forall x, In x mind -> 0 <= x < Ncol.
Hypothesis midx_leq : forall x, In x midx -> 0 <= x < Nrow.
Hypothesis mcrd_first : mcrd[0] = 0.
Hypothesis mcrd_last : mcrd[Nidx] = N.
Hypothesis mcrd_weakly_sorted : forall (i j : int), 
  (0 <= i <= Nidx) -> 
  (0 <= j <= Nidx) -> 
  (i <= j) -> 
  (mcrd[i] <= mcrd[j]).

Context (yind yval : list int).
Context (M : int).
Hypothesis len_xind : length yind = M :> int.
Hypothesis len_xval : length yval = M :> int.
Hypothesis stored_yind : sorted yind.
Hypothesis yind_leq : forall x, In x yind -> 0 <= x < Ncol.
Hypothesis Nrow0 : Nidx > 0. (* we get rid of it later *)

Definition mind_seg (row : int) := mind [[ (mcrd[row]) -- (mcrd[row + 1]) ]].

Hypothesis nodup_eachcol : forall x : int, 0 <= x < Nidx -> NoDup (mind_seg x).
Hypotheses nodup_midx : NoDup midx.

Tactic Notation "seclocal_solver" :=
  try (rewrite index_nodup=> //; math);
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
    | intros; now case_if
    | move=> >; rewrite -len_xind slice_fullE //
    | lia
    | intros; apply midx_leq, nth_In; math
    | idtac ]; auto.

Definition indexf := index.func Nidx.


(* Accessor function for uCSR format. Similar to `ucsr_get` in  Fig.2.c from the paper. 
  This encoding is a "real-world" version of the one presented in a paper. Instead of 
  storing the encoding of each row of the matrix as elements of two-dimensional arrays
  `mval` and `mind`, we concatenate them into one-dimensional arrays `mval` and `mind`
  and store an additional array `mcrd` wich says where does the eancoding of each 
  new row starts. Using this encoding the example from Fig.2.a can be represented as follows:
   
  midx :  [3, 0, 4, 3]
  
  mcrd: [0, 1,    3, 4,   6]
  mind:  [2, 1, 4, 4, 1, 3]
  mval:  [C, A, B, G, D, E] *)
Definition get (m_val : loc) := 
<{
  fun midx mind mcrd i j =>
      let i = indexf i midx in
      let "i < Nidx" = i < Nidx in
      if "i < Nidx" then
        let lb = mcrd[i] in
        let i' = i + 1 in
        let rb = mcrd[i'] in
          sv.get j mind m_val lb rb
      else 0
}>.

(* Unary specification for `ucsr_get` called outside of the `midx` array. 
  Generalised version of eq. (8) from the paper *)
Lemma get_spec_out_unary {D : Type} `{Inhab D} (m_idx m_val m_ind m_crd : loc) (i j : int) (d : D) :
  htriple (`{d}) (* The index set here is just an arbitrary singleton set `{d}` *)
    (fun=> get m_val m_idx m_ind m_crd i j) (* We run out `get` funtion on indicies `i` and `j` *)
    (\[~ In i midx] \*                      (* such that `i` ∉ midx *)
      arr(m_val, mval)⟨`d⟩ \* 
      arr(m_idx, midx)⟨`d⟩ \* 
      arr(m_ind, mind)⟨`d⟩ \* 
      arr(m_crd, mcrd)⟨`d⟩)
    (fun hr => 
     \[hr = fun=> 0] \* (* the output is the singleton hyper-value indexed by `{d}`, which is equal to 0 *)
      arr(m_val, mval)⟨`d⟩ \* 
      arr(m_idx, midx)⟨`d⟩ \* 
      arr(m_ind, mind)⟨`d⟩ \* 
      arr(m_crd, mcrd)⟨`d⟩).
Proof with seclocal_solver.
  xwp; xsimpl=> /(memNindex _)?; xapp @index.spec... (* apply index function specification *) 
  xstep; xwp; xif=> ?... (* case analysis on `i < Nidx` condition *)
  xwp; xval; xsimpl*. (* finish the proof *)
Qed.


Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition get_index := @LibWP.eld (int * int)%type.
Coercion get_index : D >-> Dom. (* `get_index` is a coercion of `labeled (int * int)` to `int * int` *)

(* Hyper specification for `ucsr_get` function, called on a set of indecies,
  outside of the `midx` array. The index set in this case is a finite 
  set (`fset`) of elements `⟨l, i, j⟩` with type `labeled (int * int)`.
  Generalised version of eq.(7) from the paper. *)
Lemma get_spec_out `{Inhab (labeled (int * int))} (fs : fset (labeled (int * int))) (m_idx m_val m_ind m_crd : loc) : 
  htriple fs
    (fun ij => get m_val m_idx m_ind m_crd ij.1 ij.2) 
    (\[forall d, indom fs d -> ~ In (get_index d).1 midx] \* (* for all `⟨l, i, j⟩` elements of `fs`, `i ∉ midx` *)
      (\*_(d <- fs) arr(m_val, mval)⟨`d⟩) \* 
      (\*_(d <- fs) arr(m_idx, midx)⟨`d⟩) \* 
      (\*_(d <- fs) arr(m_ind, mind)⟨`d⟩) \* 
       \*_(d <- fs) arr(m_crd, mcrd)⟨`d⟩)
    (fun hr => 
     \[hr = fun=> 0] \* 
      (\*_(d <- fs) arr(m_val, mval)⟨`d⟩) \*
      (\*_(d <- fs) arr(m_idx, midx)⟨`d⟩) \* 
      (\*_(d <- fs) arr(m_ind, mind)⟨`d⟩) \*  
       \*_(d <- fs) arr(m_crd, mcrd)⟨`d⟩).
Proof. by xpointwise_build (@get_spec_out_unary). Qed. (* apply `Product` rule from Fig. 4 *)


Tactic Notation "seclocal_fold" := 
  rewrite ?label_single ?wp_single
    -/(For_aux _ _) 
    -/(For _ _ _) //=.


Hypothesis sorted_eachcol : forall x : int, 0 <= x < Nidx -> sorted (mind_seg x).

(* #10 from the table
  Version of `spmspv` from Fig.3 *)
Definition spmspv m_ind y_ind m_val y_val := 
  let spvspv := sv.sv_dotprod m_ind y_ind m_val y_val in
  <{
  fun mcrd midx =>
  let s = alloc0 Nrow in
  for i <- [0, Nidx] {
    let lb = mcrd[i] in
    let i' = i + 1 in
    let rb = mcrd[i'] in
    let i = midx[i] in
    let x = spvspv lb rb 0 M in 
      s[i] := x
  }; 
  s
}>.

Notation size := length.

(**************************************************************************************)
(*********  The full verison of the proof snippet from Section 4 of the paper *********)
(**************************************************************************************)
(*
  Discrepancies with a paper version: 
  1. Instead of `xfor` tactic from the paper, we use a more convenient tactic 
    `xfor_bigstr`. This tactic takes not the whole invariant as an input, but only that
    part of it, which changes within the inductive step. Here we provide it some
    technical arguments `Inv`, `R2`, `R3`, althother with two verisions of the changed 
    clause from I_for: before and after the inductive step.
  2. The postcondtion of the triple in the paper contains `Arrs` predicate. This predicate 
    states that all arrays from the precondition are left untouched. Here, we replace it 
    with `\Top` for readability purposes.
*)

Lemma spmspv_spec `{Inhab D} `{H__ : Inhab (labeled int)}
  (m_val m_ind m_idx m_crd y_ind y_val : loc) : 
  {{ arr(m_val, mval)⟨1, (0,0)⟩ \*
     arr(m_idx, midx)⟨1, (0,0)⟩ \*
     arr(m_ind, mind)⟨1, (0,0)⟩ \*
     arr(m_crd, mcrd)⟨1, (0,0)⟩ \*
     arr(y_ind, yind)⟨1, (0,0)⟩ \* 
     arr(y_val, yval)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_val, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_idx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_ind, mind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_crd, mcrd)⟨2, i⟩) \*
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_ind, yind)⟨3, i⟩) \* 
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    {1| _  in `{(0,0)}                 => spmspv m_ind y_ind m_val y_val m_crd m_idx};
    {2| ij in `[0, Nrow] \x `[0, Ncol] => get m_val m_idx m_ind m_crd ij.1 ij.2};
    {3| zj in `{0}       \x `[0, Ncol] => sv.get zj.2 y_ind y_val 0 M}
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

(* #8 from the table
  Summation of all elements in uCSR sparse maitrix *)
Definition sum := 
  <{
    fun mval midx mind mcrd =>
    let s = ref 0 in
    for i <- [0, Nidx] {
      let lb = mcrd[i] in
      let i' = i + 1 in
      let rb = mcrd[i'] in
      let x = sv.sum mind mval lb rb in 
        s += x
    };
    ! s
}>.

(* Specification for `sum` *)
Lemma sum_spec `{Inhab D} `{Inhab (labeled int)} (m_val m_ind m_crd m_idx : loc) : 
  {{ arr(m_val, mval)⟨1, (0,0)⟩ \*
     arr(m_idx, midx)⟨1, (0,0)⟩ \*
     arr(m_ind, mind)⟨1, (0,0)⟩ \*
     arr(m_crd, mcrd)⟨1, (0,0)⟩ \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_val, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_idx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_ind, mind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_crd, mcrd)⟨2, i⟩) }}
  [{
    [1| _  in `{(0,0)}   => sum m_val m_idx m_ind m_crd];
    {2| ij in `[0, Nrow] \x `[0, Ncol] => get m_val m_idx m_ind m_crd ij.1 ij.2}
  }]
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) hv[`2](i)] \* \Top}}.
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R int Inv R 2. (* start the proof *)
  xfocus* 2 (indom (midx \x `[0, Ncol])). (* focus on non-zero getters with `Focus` rule from Fig.5 *)
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap. (* clean up the heap *)
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol]. (* simplify index sets *)
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  xin 1 : xstep=> s... (* advance the first instruction in `sum` *)
  xfor_sum Inv R R (fun hv i => Σ_(j <- `{midx[i]} \x `[0, Ncol]) hv[`2](j)) s. (* `For` rule application (Fig.6) *)
  { xin* 2: xapp* @index.specs; xstep; xwp; xif=> [?|]; xgo...  (* advance all instructions in `ucsr.get` up to `sv.get` *)
    xin 1 : xgo... (* advance `sum` up to `sv.sum` *)
    rewrite index_nodup //; try math. (* simplify index *)
    xsubst (snd : _ -> int). (* apply `Subst` rule from `Fig.7` *)
    xnapp sv.sum_spec... (*  apply specification for sparse SV vector summation *)
    xsimpl=>->. xapp @incr.spec. rewrite sum_prod1E. xsimpl. }
  { move=>Ha Hb Hc; left. move: Ha; apply contrapose, NoDup_nthZ; autos*; math. }
  xstep. xsimpl*. xsum_normalize. (* adjust summations *)
  rewrite SumCascade -?prod_Union_distr -?len_midx -?(fset_of_list_nodup 0) ?E //.
  disjointE.
  move=>Ha Hb Hc; left. move: Ha; apply contrapose, NoDup_nthZ; autos*; math.
Qed.

Context (dvec : list int).
Context (dvec_len : length dvec = Ncol :> int).

(* #9 from the table
  Dot product of a sparse uCSR matrix and a dense vector *)
Definition spmv := 
  <{
  fun mval midx mind mcrd dvec =>
  let s = alloc0 Nrow in
  for i <- [0, Nidx] {
    let lb = mcrd[i] in
    let i' = i + 1 in
    let rb = mcrd[i'] in
    let i = midx[i ]in
    let x = sv.dotprod mind mval dvec lb rb in 
    s[i] := x
  }; 
  s
}>.

(* Specification for `spmv`. Proof is similar to the one above *)
Lemma spmv_spec `{Inhab D} `{H__ : Inhab (labeled int)} (m_val m_idx m_ind m_crd x_dvec : loc) : 
  {{ arr(m_val, mval)⟨1, (0,0)⟩ \*
     arr(m_idx, midx)⟨1, (0,0)⟩ \*
     arr(m_ind, mind)⟨1, (0,0)⟩ \*
     arr(m_crd, mcrd)⟨1, (0,0)⟩ \*
     arr(x_dvec, dvec)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_val, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_idx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_ind, mind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(m_crd, mcrd)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_dvec, dvec)⟨2, i⟩) }}
  [{
    [1| _  in `{(0,0)}                 => spmv m_val m_idx m_ind m_crd x_dvec];
    {2| ij in `[0, Nrow] \x `[0, Ncol] => get m_val m_idx m_ind m_crd ij.1 ij.2}
  }]
  {{ hv,
  arrf(hv[`1]((0, 0)), i0 in Nrow=> Σ_(j0 <- `[0, Ncol]) hv[`2]((i0, j0)) * dvec[j0])⟨1, (0, 0)⟩
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

End unordered_csr.

End unordered_csr.
