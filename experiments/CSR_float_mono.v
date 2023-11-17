Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibDotprod_float LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl LibArray LibLoops LibLoops_float Subst NTriple.
From LGTM.lib.theory Require Import LibListExt.
From LGTM.experiments Require Import Prelude UnaryCommon.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Module sv_float.

Section sv.

Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
(* sometimes Coq cannot tell whether lb is a variable or an int, so avoid using the same name lb here *)
Notation "'xlb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'xrb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.

Import List Vars list_interval_notation.

Context (xind : list int).
Context (xval : list binary64).
Context (N M : int).
Context (lb rb : int).
Hypothesis (len : rb - lb = N).
Hypotheses (bounds_l: 0 <= lb) (bounds_r: lb <= rb).
Hypothesis len_xind : rb <= length xind.
Hypothesis len_xval : rb <= length xval.
Hypothesis nodup_xind : NoDup (xind [[ lb -- rb ]]).
Hypothesis sorted_xind : sorted (xind [[ lb -- rb ]]). (* TODO possibly remove nodup_xind since sorted_xind subsumes it? *)
Hypothesis xind_leq : forall x, In x (xind [[ lb -- rb ]]) -> 0 <= x < M.
Hypothesis xval_finite : forall x, In x (xval [[ lb -- rb ]]) -> @finite Tdouble x.

Tactic Notation "seclocal_solver" :=
  first [ rewrite list_interval_nth'; auto; math
    | rewrite list_interval_length; auto; math
    | rewrite -list_interval_nth; auto; math
    | idtac ]; auto.

Definition indexf := index_bounded.func.

Definition get := 
  <{
  fun i xind xval xlb xrb =>
    let k = indexf xlb xrb i xind in 
    let "k < rb" = k < xrb in
    if "k < rb" then
      xval[.k]
    else float_unit
}>.

Lemma get_spec_in {D : Type} `{Inhab D} (x_ind x_val : loc) i d : 
  @htriple D (single d tt) 
    (fun=> get (List.nth (abs i) (xind [[ lb -- rb ]]) 0) x_ind x_val lb rb)
    (\[0 <= i < N] \*
      harray_int xind x_ind d \* 
      harray_float xval x_val d)
    (fun hr => 
     \[hr = fun=> List.nth (abs i) (xval [[ lb -- rb ]]) float_unit] \* 
      harray_int xind x_ind d \* 
      harray_float xval x_val d).
Proof with seclocal_solver.
  xwp; xsimpl=> ?; xapp (@index_bounded.spec _ H)=> //.
  xwp; xapp. rewrite index_nodup; auto...
  xwp; xif=> ?; subst; try math.
  xapp; xsimpl*...
Qed.

Lemma get_spec_out_unary {D : Type} `{Inhab D} (x_ind x_val : loc) (i : int) d : 
  @htriple D (single d tt) 
    (fun=> get i x_ind x_val lb rb)
    (\[~ In i (xind [[ lb -- rb ]])] \*
      harray_int xind x_ind d \* 
      harray_float xval x_val d)
    (fun hr => 
     \[hr = fun=> float_unit] \* 
      harray_int xind x_ind d \* 
      harray_float xval x_val d).
Proof.
  xwp; xsimpl=> ?; xapp (@index_bounded.spec _ H)=> //...
  rewrite memNindex // list_interval_length //.
  xwp; xapp. xwp; xif=> ?; try math. xwp; xval. xsimpl*.
Qed.

Local Notation D := (labeled int).

Lemma get_spec_out `{Inhab D} fs (x_ind x_val : loc) : 
  @htriple D fs
    (fun i => get (eld i) x_ind x_val lb rb)
    (\[forall d, indom fs d -> ~ In (eld d) (xind [[ lb -- rb ]])] \*
      (\*_(d <- fs) harray_int xind x_ind d) \* 
       \*_(d <- fs) harray_float xval x_val d)
    (fun hr => 
     \[hr = fun=> float_unit] \* 
      ((\*_(d <- fs) harray_int xind x_ind d) \* 
       \*_(d <- fs) harray_float xval x_val d)).
Proof. by xpointwise_build (@get_spec_out_unary). Qed.

End sv. 

End sv_float.

Module csr_float.

Section csr.

Notation "'mval'" := ("m_val":var) (in custom trm at level 0) : trm_scope.
Notation "'colind'" := ("col_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'rowptr'" := ("row_ptr":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
Notation "'lb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'rb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.
Notation "'i''" := ("i_'":var) (in custom trm at level 0) : trm_scope.

Import List Vars list_interval_notation.

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
  (rowptr[i] <= rowptr[j]).
Hypothesis mval_finite : forall x, In x mval -> @finite Tdouble x.

Definition colind_seg (row : int) := colind [[ (rowptr[row]) -- (rowptr[row + 1]) ]].

Hypothesis nodup_eachcol : forall x : int, 0 <= x < Nrow -> NoDup (colind_seg x).
Hypothesis sorted_eachcol : forall x : int, 0 <= x < Nrow -> sorted (colind_seg x). 

Local Tactic Notation "seclocal_solver" :=
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

Definition get := 
<{
  fun mval colind rowptr i j =>
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
      sv_float.get j colind mval lb rb
}>.

Tactic Notation "seclocal_fold" := 
  rewrite ?label_single ?wp_single
    -?/(harray_float _ _ _)
    -?/(harray_int _ _ _)
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition eld := @LibWP.eld (int * int)%type.
Coercion eld : D >-> Dom.

Context (dvec : list binary64).
Context (dvec_len : length dvec = Ncol :> int).
Hypothesis dvec_finite : forall x, In x dvec -> @finite Tdouble x.

Section spmv_monolithic.

Definition spmv := 
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

Tactic Notation "seclocal_solver2" :=
  first [ rewrite /colind_seg list_interval_nth'; auto; solve [ math | seclocal_solver ]
    | rewrite /colind_seg list_interval_length; auto; solve [ math | seclocal_solver ]
    | rewrite /colind_seg -list_interval_nth; auto; solve [ math | seclocal_solver ]
    | idtac ]; auto.

Lemma spmv_spec `{Inhab (labeled int)} `{Inhab D} (x_mval x_colind x_rowptr x_dvec : loc) : 
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
  {{ hv, 
  harray_fun_float'  
    (fun i => (Sum_fma float_unit (lof id Ncol) (fun j => (to_float (hv[`2]((i, j))), dvec[j]))))
    (hv[`1]((0,0))) Nrow (Lab (1,0) (0,0)) \* \Top }}.
Proof with (try solve [ seclocal_solver | seclocal_solver2 | auto using finite_suffcond ]; seclocal_fold; try lia).
  xset_Inv Inv 1; xset_R Dom Inv R 2.
  xin 2 : do 3 (xwp; xapp).
  xin 1 : (xwp; xapp (@htriple_allocf0_unary)=> // s; xwp; xapp)...
  rewrite prod_cascade.
  xfor_arrayset Inv R R (fun hv i => (Sum_fma float_unit (lof id Ncol) (fun j => (to_float (hv[`2]((i, j))), dvec[j])))) (fun=> float_unit) s.
  { xin 2 : rewrite wp_prod_single /=...
    xin 1 : (xwp; xapp=> tmp; do 3 (xwp; xapp))...
    xsubst (snd : _ -> int)...
    clear Inv R. xset_Inv Inv 1 tmp. xset_R int Inv R 2%Z.
    xfocus* 2 (colind_seg l0).
    xapp_big sv_float.get_spec_out... 1: case=>??; indomE; autos*.
    xin 1 : idtac.
    have Hl : length (colind_seg l0) = rowptr[l0 + 1] - rowptr[l0] :> int...
    rewrite intr_list ?(fset_of_list_nodup 0) ?Hl ?Union_interval_change2...
    rewrite -> ! hbig_fset_hstar; xclean_heap.
    xfor_sum Inv R R (fun hv i => (to_float (hv[`2](colind[i])), dvec[colind[i] ])) tmp...
    { (xin 1: do 3 (xwp; xapp); xapp (@fma.spec)=> y)... 
      xapp (@sv_float.get_spec_in)=> //; try math... xsimpl*...
      rewrite list_interval_nth'... }
    { move=> ??? HH. eapply (proj1 (NoDup_nthZ _ _) (nodup_eachcol H1)) in HH... }
    move=> /= Hfin; xwp; xapp... xwp; xapp; xapp; xsimpl.
    rewrite -/(Sum_fma _ _ _) Sum_fma_lof ?Sum_fma_filter_If'; try intro;
    rewrite -?sorted_bounded_sublist ?Sum_fma_list_interval ?In_lof_id //...
    move: (indexG0 a0 (colind_seg l0)); rewrite /LibSummation.mem=> ??.
    move=> /[dup] /(nth_index 0){2}<-; rewrite -index_mem=> ?.
    rewrite -list_interval_nth; try apply/(Hfin _ _).1... }
  { apply Sum_fma_feq=>? /In_lof_id ? /= /[! hvE]; indomE... }
  xwp; xval. xsimpl*.
Qed.

End spmv_monolithic.

End csr.

End csr_float.
