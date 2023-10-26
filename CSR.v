Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer.
From SLF Require Import Struct Loops Unary_IndexWithBounds SV2 Subst NTriple Loops2 Struct2.
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
Notation "'lb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'rb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.
Notation "'i''" := ("i_'":var) (in custom trm at level 0) : trm_scope.

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
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Lemma wp_prod_single {A B : Type} s fs Q ht (l : labType):
  @wp (labeled (A * B)) (label (Lab l (`{s} \x fs))) ht Q = 
  @wp (labeled (A * B)) (label (Lab l (`{s} \x fs))) (fun ld => ht(Lab l (s, (eld ld).2))) Q.
Proof.
Admitted.

Lemma in_interval_list {A : Type} (l : list A) lb rb x: 
   In x (list_interval lb rb l) -> In x l.
Proof.
Admitted.

Arguments in_interval_list {_ _ _ _ _}.

Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition eld := @LibWP.eld (int * int)%type.
Coercion eld : D >-> Dom.


Lemma hstar_fset_prod1fs {A B D : Type} (l : A) (fs : fset B) : 
  hbig_fset hstar (`{l} \x fs) = 
  fun Q : _ -> hhprop D => \*_(d <- fs) (Q (l, d)).
Proof.
  apply/fun_ext_1=> Q.
  elim/fset_ind: fs. 
  { by rewrite prodfs0 ?hbig_fset_empty. }
  move=> fs x IH ?; rewrite prodfsS hbig_fset_union //.
  { by rewrite hbig_fset_update // IH prod11 hstar_fset_label_single. }
  apply/disjoint_of_not_indom_both=> -[]??; rewrite ?indom_prod /= ?indom_single_eq.
  by case=> ?<-[_].
Qed.

Global Instance Inhab_lab_int : Inhab (labeled int).
split. by exists (Lab (0,0) 0). Qed.

Hint Rewrite @hstar_fset_prod1fs : hstar_fset.
Hint Rewrite @indom_label_eq @indom_union_eq @indom_prod @indom_interval @indom_single_eq : indomE.

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
    xapp @incr.spec.
    unfold prod; rewrite -SumCascade ?Sum1 -?SumCascade; try by disjointE.
    erewrite SumEq with (fs:=`[0, Ncol]). 1: xsimpl*.
    move=>* /=; by rewrite Sum1. }
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

(* TODO possibly, reuse some parts from xfor_sum? *)
Tactic Notation "xfor_specialized" constr(Inv) constr(R) uconstr(R') uconstr(op) uconstr(f) constr(s) :=
  eapply (@xfor_lemma_gen_array_fun _ _ Inv R R' _ _ _ s f op);
  [ try math
  | intros ??; rewrite ?/Inv ?/R ?/R';
    xnsimpl
  | 
  |
  |
  | let hvE := fresh "hvE" in
    let someindom := fresh "someindom" in
    intros ???? hvE; rewrite ?/op; indomE;
    match goal with 
    | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ?; indomE; intros someindom; extens; intros 
    | _ => idtac
    end; try setoid_rewrite hvE; [eauto|autorewrite with indomE; try math; 
      (first [ apply someindom | idtac ])]
  |
  |
  |
  |
  |
  |
  |
  |
  | rewrite ?/Inv ?/R; rewrite -> ?hbig_fset_hstar; xsimpl
  | intros ?; rewrite ?/Inv ?/R' ?/op; rewrite -> ?hbig_fset_hstar; xsimpl
  ]=> //; try (solve [ rewrite ?/Inv ?/R ?/R' /=; xlocal ]); autos*.

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
    harray_fun (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * dvec[j]) p Nrow (Lab (1,0) (0,0)))
      \* \Top }}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver).
  xin (2,0) : do 3 (xwp; xapp).
  xfocus (1,0). (* TODO xin does not work here. why? *)
  xwp; xapp (@htriple_alloc0_unary); try assumption.
  intros ss s Es... rewrite Es. clear ss Es. rewrite <- label_single.
  xunfocus.
  rewrite prod_cascade.
  set (R (i : Dom) := 
    arr(x_mval, mval)⟨2, i⟩ \*
    arr(x_colind, colind)⟨2, i⟩ \* 
    arr(x_rowptr, rowptr)⟨2, i⟩ \*
    arr(x_dvec, dvec)⟨2, i⟩).
  set (Inv (i : int) := 
    arr(x_mval, mval)⟨1, (0,0)⟩ \* 
    arr(x_colind, colind)⟨1, (0,0)⟩ \* 
    arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
    arr(x_dvec, dvec)⟨1, (0,0)⟩).
  xfor_specialized Inv R R (fun hv i => Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * dvec[j.2])) (fun=> 0) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xframe2 (arr(x_rowptr, rowptr)⟨1, (0, 0)⟩).
    xsubst (snd : _ -> int).
    xnapp sv.dotprod_spec...
    { move=> ?/in_interval_list... }
    move=> ?; rewrite -wp_equiv. xsimpl=>->.
    xapp @lhtriple_array_set_pre; try math.
    unfold prod; rewrite -SumCascade ?Sum1 -?SumCascade; try by disjointE.
    erewrite SumEq with (fs:=`[0, Ncol]). 1: xsimpl*.
    move=>* /=; by rewrite Sum1. }
  { xwp; xval. xsimpl*. 
    (* just by funext *)
    replace (fun i0 : int => Σ_(j0 <- `{i0} \x `[0, Ncol]) hv[`2](j0) * dvec[j0.2]) with
      (fun i0 : int => Σ_(j0 <- `[0, Ncol]) hv[`2]((i0, j0)) * dvec[j0]).
    1: xsimpl*.
    extens=> ?.
    (* TODO why repeating above here? *)
    unfold prod; rewrite -SumCascade ?Sum1 -?SumCascade; try by disjointE.
    erewrite SumEq with (fs:=`[0, Ncol]). 1: reflexivity.
    move=>* /=; by rewrite Sum1. }
Qed.

End csr.

End csr.
