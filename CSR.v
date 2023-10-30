Set Implicit Arguments.
(* Require Export Setoid.
Require Export Relation_Definitions.

Locate "_ ==> _ ==> _". Check Morphisms.respectful. *)

From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer ListCommon.
From SLF Require Import Struct Loops Unary_IndexWithBounds SV Subst NTriple Loops2 Struct2.
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


Lemma in_interval_list {A : Type} (l : list A) lb rb x: 
   In x (list_interval lb rb l) -> In x l.
Proof.
Admitted.

Arguments in_interval_list {_ _ _ _ _}.

Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition eld := @LibWP.eld (int * int)%type.
Coercion eld : D >-> Dom.

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
    harray_fun (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * dvec[j]) p Nrow (Lab (1,0) (0,0)))
      \* \Top }}. (* this \Top can be made concrete, if needed *)
Proof with (try seclocal_fold; seclocal_solver).
  xin (2,0) : do 3 (xwp; xapp).
  xin (1,0) : (xwp; xapp (@htriple_alloc0_unary)=> // s)...
  rewrite prod_cascade.
  set (R (i : Dom) := arr(x_mval, mval)⟨2, i⟩ \*
    arr(x_colind, colind)⟨2, i⟩ \* 
    arr(x_rowptr, rowptr)⟨2, i⟩ \*
    arr(x_dvec, dvec)⟨2, i⟩).
  set (Inv (i : int) := arr(x_mval, mval)⟨1, (0,0)⟩ \* 
    arr(x_colind, colind)⟨1, (0,0)⟩ \* 
    arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
    arr(x_dvec, dvec)⟨1, (0,0)⟩).
  xfor_specialized_normal Inv R R (fun hv i => Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * dvec[j.2])) (fun=> 0) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xframe2 (arr(x_rowptr, rowptr)⟨1, (0, 0)⟩).
    xsubst (snd : _ -> int).
    xnapp sv.dotprod_spec...
    { move=> ?/in_interval_list... }
    move=> ?; rewrite -wp_equiv. xsimpl=>->.
    xapp @lhtriple_array_set_pre; try math.
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

Lemma Union_same {B C} (v : int) (f : fmap B C) : 
  v > 0 -> 
    Union `[0, v] (fun=> f) = f.
Admitted.

Arguments Union_same {_ _} _ _.

Tactic Notation "xfor_specialized_normal" constr(Inv) constr(R) uconstr(R') uconstr(op) uconstr(f) constr(s) :=
  eapply (@xfor_lemma_gen_array_fun_normal _ _ Inv R R' _ _ _ s f op);
  [ intros ??; rewrite ?/Inv ?/R ?/R';
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
  | try lia
  |
  |
  |
  |
  |
  |
  | rewrite ?/Inv ?/R; rewrite -> ?hbig_fset_hstar; xsimpl
  | intros ?; rewrite ?/Inv ?/R' ?/op; rewrite -> ?hbig_fset_hstar; xsimpl
  ]=> //; try (solve [ rewrite ?/Inv ?/R ?/R' /=; xlocal ]); autos*.

Tactic Notation "xsubst" uconstr(f) := 
  rewrite /ntriple;
  match goal with 
  | |- _ ==> N-WP [{
    [?i| _ in ?fs1 => _];
    [?j| _ in ?fs2 => _]
  }] {{ _ , _}} => 
    let Inj := fresh in 
    have Inj : 
      forall x y, 
        indom (⟨(i,0), fs1⟩ \u ⟨(j,0), fs2⟩) x -> 
        indom (⟨(i,0), fs1⟩ \u ⟨(j,0), fs2⟩) y -> 
        Lab (lab x) (f (el x)) = Lab (lab y) (f (el y)) -> x = y; 
        [ try (intros [?[??] ][?[??] ]; indomE=> /= + /[swap]=>/[swap]-[]->-> []?[]; eqsolve)
        | eapply (@xntriple2_hsub _ _ f); 
          [ by []
          | eapply Inj
          | xlocal 
          | xlocal
          | case=> ??/=; reflexivity
          | case=> ??/=; reflexivity
          | xsubst_rew Inj; indomE; autos*
          | move=> ? /=; xsubst_rew Inj; indomE; autos*
          |
          ]
        ]
  | |- _ ==> N-WP [{
    [?i| _ in ?fs1 => _];
    [?j| _ in ?fs2 => _];
    [?k| _ in ?fs3 => _]
  }] {{ _ , _}} => 
  let Inj := fresh in 
  have Inj : 
    forall x y, 
      indom (⟨(i,0), fs1⟩ \u ⟨(j,0), fs2⟩ \u ⟨(k,0), fs3⟩) x -> 
      indom (⟨(i,0), fs1⟩ \u ⟨(j,0), fs2⟩ \u ⟨(k,0), fs3⟩) y -> 
      Lab (lab x) (f (el x)) = Lab (lab y) (f (el y)) -> x = y; 
      [ try (intros [?[??] ][?[??] ]; indomE=> /= + /[swap]=>/[swap]-[]->-> []?[]; eqsolve)
        | eapply (@xntriple3_hsub _ _ f); 
          [ by []
          | by []
          | by []
          | eapply Inj
          | xlocal 
          | xlocal
          | case=> ??/=; reflexivity
          | case=> ??/=; reflexivity
          | case=> ??/=; reflexivity
          | xsubst_rew Inj; indomE; autos*
          | move=> ? /=; xsubst_rew Inj; indomE; autos*
          |
          ]
        ]
  end; rewrite /labf_of; simpl; fsubstE.

Tactic Notation "xnapp" constr(E) := 
  rewrite -> ?hbig_fset_hstar;
  apply/xletu2=> //=; [eapply xnapp_lemma'; 
       [eapply E|rewrite /arr1;
         let hp := fresh "hp" in 
         let HE := fresh "HE" in 
        remember hpure as hp eqn:HE;
       xapp_simpl=> ?; rewrite HE; exact: himpl_refl]|]; eauto; simpl.

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
  eapply (@xfor_lemma_gen_array_fun_normal2 _ _ 
   Inv R1 R1 R2 R2 _ _ _ _ s (fun=> 0)
   (fun hv i => Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * hv[`3]((0, j.2)))))=> //; try eassumption.
  { intros ??; rewrite ?/Inv ?/R1 ?/R2; xnsimpl.
    xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xframe2 (arr(x_rowptr, rowptr)⟨1, (0, 0)⟩).
    xsubst (snd : _ -> int).
    xnapp @sv.sv_dotprod_spec... 
    { admit. }
    { admit. }
    { admit. }
    { admit. }  
    move=> ?; rewrite -wp_equiv. xsimpl=>->.
    xapp @lhtriple_array_set_pre; try math.
    rewrite sum_prod1E; xsimpl. }
  { rewrite /Inv. xlocal. }
  { rewrite /R1. xlocal. }
  { rewrite /R1. xlocal. }
  { rewrite /R2. xlocal. }
  { rewrite /R2. xlocal. }
  { let hvE1 := fresh "hvE1" in
    let hvE2 := fresh "hvE2" in
    let someindom := fresh "someindom" in
    intros ???? hvE1 hvE2; rewrite ?/op; indomE;
    match goal with 
    | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ?; indomE; intros someindom; extens; intros 
    | _ => idtac
    end; try rewrite hvE1 1?hvE2;
     [eauto|autorewrite with indomE; try math; 
      (first [ apply someindom | idtac ])| autorewrite with indomE; try math; 
      (first [ apply someindom | idtac ])]; simpl; try lia. }
  { rewrite ?/Inv ?/R1 /R2. rewrite -> ?hbig_fset_hstar; xsimpl.
    rewrite Union_same //; xsimpl*. }
  intros ?; rewrite ?/Inv ?/R1 /R2 ?/op; rewrite -> ?hbig_fset_hstar; xsimpl.
  xwp; xval. xsimpl*. xsimpl; rewrite sum_prod1E; xsimpl.
Admitted.


End csr.

End csr.
