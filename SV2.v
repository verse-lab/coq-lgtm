Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops Unary_IndexWithBounds.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.


Definition to_int (v : val) : int := 
  match v with 
  | val_int i => i 
  | _ => 0
  end.

Coercion to_int : val >-> Z.

Lemma to_int_if P a b : 
  to_int (If P then a else b) = If P then a else b.
Proof. by case: classicT. Qed.

Section pure_facts.

Import List.

Lemma NoDup_nthZ {A : Type} i j l (z : A): 
  NoDup l <->
  ((0<= i < Datatypes.length l) ->
  (0<= j < Datatypes.length l) -> nth (abs i) l z = nth (abs j) l z -> i = j).
Admitted.

Lemma in_combineE {A B : Type} (l : list A) (l' : list B) (x : A) (y : B) :
  In (x, y) (combine l l') = (In x l /\ In y l').
Admitted.

End pure_facts.

Module sv.

Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.

Section sv.

Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
(* sometimes Coq cannot tell whether lb is a variable or an int, so avoid using the same name lb here *)
Notation "'xlb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'xrb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.

Import List Vars.

Context (xind xval : list int).
Context (N M : int).
Context (lb rb : int).
Hypothesis (len : rb - lb = N).
(* Hypothesis (bounds: 0 <= lb <= rb). *) (* TODO generalize_arith will loop if bounds is present *)
Hypotheses (bounds_l: 0 <= lb) (bounds_r: lb <= rb).
Hypothesis len_xind : rb <= length xind.
Hypothesis len_xval : rb <= length xval.
Hypothesis nodup_xind : NoDup (list_interval (abs lb) (abs rb) xind).
Hypothesis xind_leq : forall x, In x (list_interval (abs lb) (abs rb) xind) -> 0 <= x < M.

Definition indexf := index_bounded.func.

Definition get := 
  <{
  fun i xind xval xlb xrb =>
    let k = indexf xlb xrb i xind in 
    let "k < rb" = k < xrb in
    if "k < rb" then
      read_array xval k
    else 0
}>.

Lemma get_spec_in {D : Type} `{Inhab D} (x_ind x_val : loc) i d : 
  @htriple D (single d tt) 
    (fun=> get (List.nth (abs i) (list_interval (abs lb) (abs rb) xind) 0) x_ind x_val lb rb)
    (\[0 <= i < N] \*
      harray_int xind x_ind d \* 
      harray_int xval x_val d)
    (fun hr => 
     \[hr = fun=> List.nth (abs i) (list_interval (abs lb) (abs rb) xval) 0] \* 
      harray_int xind x_ind d \* 
      harray_int xval x_val d).
Proof.
  rewrite -wp_equiv; xsimpl=> ?.
  xwp; xapp (@index_bounded.spec _ H)=> //.
  xwp; xapp.
  rewrite index_nodup; auto.
  2: rewrite list_interval_length; subst; auto.
  xwp; xif=> ?; subst; try math.
  xapp; xsimpl*. rewrite -> list_interval_nth with (rb:=rb); try math; auto.
Qed.

Lemma get_spec_out_unary {D : Type} `{Inhab D} (x_ind x_val : loc) (i : int) d : 
  @htriple D (single d tt) 
    (fun=> get i x_ind x_val lb rb)
    (\[~ In i (list_interval (abs lb) (abs rb) xind)] \*
      harray_int xind x_ind d \* 
      harray_int xval x_val d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      harray_int xind x_ind d \* 
      harray_int xval x_val d).
Proof.
  rewrite -wp_equiv; xsimpl=> ?.
  xwp; xapp (@index_bounded.spec _ H)=> //...
  rewrite memNindex // list_interval_length //.
  xwp; xapp. xwp; xif=> ?; try math. xwp; xval. xsimpl*.
Qed.

Local Notation D := (labeled int).

Lemma get_spec_out `{Inhab D} fs (x_ind x_val : loc) : 
  @htriple D fs
    (fun i => get (eld i) x_ind x_val lb rb)
    (\[forall d, indom fs d -> ~ In (eld d) (list_interval (abs lb) (abs rb) xind)] \*
      (\*_(d <- fs) harray_int xind x_ind d) \* 
       \*_(d <- fs) harray_int xval x_val d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      ((\*_(d <- fs) harray_int xind x_ind d) \* 
       \*_(d <- fs) harray_int xval x_val d)).
Proof.
  apply/htriple_val_eq/htriple_conseq;
  [|eauto|move=> ?]; rewrite -hstar_fset_pure -?hbig_fset_hstar; first last.
  { move=> ?; apply: applys_eq_init; reflexivity. }
  apply/htriple_union_pointwise=> [> -> //|??]. 
  rewrite -wp_equiv wp_single; xapp (@get_spec_out_unary D)=> // ??->.
  xsimpl*.
Qed.

Definition sum := 
  <{
  fun xind xval xlb xrb =>
  let s = ref 0 in
  for i <- [xlb, xrb] {
    let x = read_array xval i in 
    s += x
  };
  let "res" = ! s in
  free s;
  "res"
}>.

(* Tactic Notation "xin" constr(S1) ":" tactic(tac) := 
  let n := constr:(S1) in
  xfocus n; tac; try(
  first [xunfocus | xcleanup n]; simpl; try apply xnwp0_lemma). *)
Lemma val_int_eq i j : 
  (val_int i = val_int j) = (i = j).
Proof. by extens; split=> [[]|]->. Qed.

Ltac fold' := 
  rewrite ?label_single ?wp_single ?val_int_eq
    (* -/(incr _)  *)
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Fact Union_interval_change2 [A : Type] (f : int -> fset A) (a b : int) :
  Union (interval 0 (b - a)) f = Union (interval a b) (fun i => f (i - a)).
Proof. 
  rewrite -> Union_interval_change with (c := a).
  do ? f_equal; lia.
Qed.

Fact Sum_interval_change2 (f : int -> int) (a b : int) :
  Sum (interval 0 (b - a)) f = Sum (interval a b) (fun i => f (i - a)).
Proof.
  rewrite -> Sum_interval_change with (c := a).
  do ? f_equal; lia.
Qed.

Fact Sum1 {A : Type} (s : A) (f : A -> int) : 
  Sum (`{s}) f = f s.
Proof.
  rewrite update_empty SumUpdate; [ rewrite Sum0 Z.add_0_l; reflexivity | auto ].
Qed.

Fact Sum_list_interval  (f : int -> int) (a b : int) l:
  NoDup (list_interval (abs a) (abs b) l) ->
  Sum (list_interval (abs a) (abs b) l) f = 
  Sum `[a, b] (fun i => f l[i]).
Admitted.

Fact intr_list (a b : int) (l: list int) : 
  (forall x, In x l -> a <= x < b) ->
  `[a, b] ∩ l = l.
Admitted.

Lemma lhtriple_free : forall (p : loc) (v : val) fs,
  @htriple D fs (fun d => val_free p)
    (\*_(d <- fs) p ~(d)~> v)
    (fun _ => \[]).
Proof using. intros. apply htriple_free. Qed.

Hint Resolve lhtriple_free : lhtriple.

Notation "l '[[' i '--' j ']]' " := (list_interval (abs i) (abs j) l) (at level 5).

Lemma sum_spec `{Inhab D} (x_ind x_val : loc) (s : int) : 
  {{ arr(x_ind, xind)⟨1, 0⟩ \*
     arr(x_val, xval)⟨1, 0⟩ \\* 
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) }}
  [{
    [1| ld in `{0}         => sum x_ind x_val lb rb];
    {2| ld in `[0, M]          => get ld x_ind x_val lb rb}
  }]
  {{ hv, (\[hv[`1](0) = Σ_(i <- `[0, M]) hv[`2](i)] \* 
      arr(x_ind, xind)⟨1, 0⟩ \*
      arr(x_val, xval)⟨1, 0⟩) \* 
      (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
      (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩)}}.
Proof with fold'.
  xfocus (2,0) xind[[lb -- rb]].
  rewrite (hbig_fset_part (`[0, M]) xind[[lb -- rb]]). (* TODO: move to xfocus *)
  xapp get_spec_out=> //.
  { case=> ? d0 /[! @indom_label_eq]-[_]/=.
    rewrite /intr filter_indom indom_interval /Sum.mem //=. tauto. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); set (H2 := hbig_fset hstar (_ ∖ _) _).
  xframe2 H1. xframe2 H2. xsimpl.
  xin (1,0) : xwp; xapp=> q...
  have Hl : length xind[[lb -- rb]] = rb - lb :> int.
  1: rewrite -> list_interval_length; try math.
  (* this alignment is tedious *)
  (* have E : (`[0, M]) ∩ (list_interval (abs lb) (abs rb) xind) = 
    \U_(i <-  `[0, rb - lb]) `{(list_interval (abs lb) (abs rb) xind)[i]}.
  { apply fset_extens. intros c.
    rewrite /intr filter_indom /Sum.mem indom_interval indom_Union.
    setoid_rewrite indom_interval.
    setoid_rewrite indom_single_eq.
    split.
    { intros (Hc & Hin).
      exists (index c (list_interval (abs lb) (abs rb) xind)).
      rewrite nth_index; try assumption.
      rewrite <- index_mem, -> Hl in Hin.
      split; [ split; [ apply indexG0 | assumption ] | reflexivity ]. }
    { intros (f & Hf & E). subst c.
      apply conj_dup_r; eauto. apply nth_In; math. }
  } *)
  rewrite intr_list ?(fset_of_list_nodup 0) ?Hl ?Union_interval_change2 //.
  set (R (i : int) := arr(x_ind, xind)⟨2, i⟩ \* arr(x_val, xval)⟨2, i⟩).
  set (Inv (i : int) := arr(x_ind, xind)⟨1, 0⟩ \* arr(x_val, xval)⟨1, 0⟩).
  xfor_sum Inv R R (fun hv i => hv[`2](xind[i])) q.
  { rewrite /Inv.
    (xin (1,0): (xwp; xapp; xapp (@incr.spec  _ H)=> y))...
    xapp (@get_spec_in D)=> //; try math. xsimpl*.
    rewrite <- list_interval_nth with (l:=xval); try math.
    replace (lb + (l0 - lb)) with l0 by math. xsimpl*. }
  { intros Hneq Hi Hj Hq. apply Hneq. 
    enough (abs (i0 - lb) = abs (j0 - lb) :> nat) by math.
    eapply NoDup_nth. 4: apply Hq. all: try math; try assumption. }  
  { rewrite -list_interval_nth; try f_equal; lia. }
  xwp; xapp... xwp; xapp. xwp; xval. xsimpl*.
  f_equal; under (@SumEq _ _ _ (`[0, M])).
  { move=>*; rewrite to_int_if; over. }
  rewrite SumIf intr_list // Sum0s Sum_list_interval //; math.
Qed.
(*
Context (dvec : list int).
Context (dvec_len : length dvec = M :> int).

Definition dotprod := 
  <{
  fun xind xval dvec =>
  let s = ref 0 in
  for i <- [0, N] {
    let x = xval[i] in 
    let i = xind[i] in 
    let v = dvec[i] in 
    let x = x * v in
    s += x
  };
  ! s
}>.

Lemma SumIf {A : Type} {P : A -> Prop} {fs F G} (C : A -> int -> int) : 
  (Σ_(i <- fs) C i (If P i then F i else G i)) = 
  Σ_(i <- fs ∩ P) C i (F i) + Σ_(i <- fs ∖ P) C i (G i).
Proof using.
Admitted.

Lemma dotprod_spec `{Inhab D} (x_ind x_val d_vec : loc) : 
  {{ arr(x_ind, xind)⟨1, 0⟩ \\*
     arr(x_val, xval)⟨1, 0⟩ \\*
     arr(d_vec, dvec)⟨1, 0⟩ \\* 
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, M]) arr(d_vec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{0}   => dotprod x_ind x_val d_vec];
    [2| ld in `[0,M] => get ld x_ind x_val]
  }]
  {{ hv, \[hv[`1](0) = Σ_(i <- `[0,M]) (hv[`2](i) * dvec[i])] \* \Top}}.
Proof with fold'.
  xfocus (2,0) xind.
  rewrite (hbig_fset_part `[0, M] xind). (* TODO: move to xfocus *)
  xapp get_spec_out=> //.
  { case=> ?? /[! @indom_label_eq]-[_]/=; rewrite /intr filter_indom; autos*. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); 
  set (H2 := hbig_fset hstar (_ ∖ _) _).
  set (H3 := hbig_fset hstar (_ ∖ _) _).
  xframe (H1 \* H2 \* H3); clear H1 H2 H3.
  xin (1,0) : xwp; xapp=> s...
  have E : `[0,M] ∩ xind = xind.
  { apply/fset_extens=> x; rewrite /intr filter_indom -fset_of_list_in; splits*.
    move=> ?; splits*; rewrite* indom_interval. }
  rewrite E (fset_of_list_nodup 0) // len_xind.
  set (R i := arr(x_ind, xind)⟨2, i⟩ \* arr(x_val, xval)⟨2, i⟩ \* arr(d_vec, dvec)⟨2,i⟩).
  set (Inv (i : int) := arr(x_ind, xind)⟨1, 0⟩ \* arr(x_val, xval)⟨1, 0⟩ \* arr(d_vec, dvec)⟨1,0⟩).
  xfor_sum Inv R (fun=> \Top) (fun hv i => (hv[`2](xind[i]) * dvec[xind[i] ])) s.
  { rewrite /Inv /R.
    (xin (1,0): do 4 (xwp; xapp); xapp incr.spec=> y)...
    xapp get_spec_in=> //; xsimpl*. }
  { move=> Neq ???; apply/Neq. 
    move/NoDup_nthZ: nodup_xind; apply; autos*; math. }
  { rewrite -len_xind; math. }
  xapp; xsimpl.
  under (@SumEq _ _ _ `[0,M]).
  { move=>*; rewrite to_int_if; over. }
  rewrite (SumIf (fun=> Z.mul^~ _)) E (SumList 0) // len_xind Sum0s; math.
Qed.
*)
End sv.


End sv.

(*

Module coo. 

Module Export AD2 := WithUnary(Int2Dom).

Lemma hbig_fset_part {A : Type} (fs : fset A) (P : A -> Prop) : 
  hbig_fset hstar fs = 
  fun H => hbig_fset hstar (fs ∩ P) H \* hbig_fset hstar (fs ∖ P) H.
Proof.
  apply/fun_ext_1=> ?; rewrite -hbig_fset_union // ?fs_pred_part //.
  exact/fs_pred_part_disj.
Qed.

Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.


Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Section coo.

Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
Notation "'xrow'" := ("x_row":var) (in custom trm at level 0) : trm_scope.
Notation "'xcol'" := ("x_col":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.

Import List Vars.

Context (xrow xcol xval : list int).
Context (N Nrow Ncol : int).
Hypothesis len_xrow : length xrow = N :> int.
Hypothesis len_xcol : length xcol = N :> int.
Hypothesis len_xval : length xval = N :> int.
Hypothesis nodup_xrowcol : NoDup (combine xrow xcol).
Hypothesis xrow_leq : forall x, In x xrow -> 0 <= x < Nrow.
Hypothesis xcol_leq : forall x, In x xcol -> 0 <= x < Ncol.

Definition indexf := index2.func N.

Definition get := 
  <{
  fun i j xrow xcol xval =>
    let k = indexf i j xrow xcol in 
    read_array xval k
}>.

Lemma get_spec_in `{Inhab D} (x_row x_col x_val : loc) i d : 
  htriple (single d tt) 
    (fun=> get (List.nth (abs i) xrow 0) (List.nth (abs i) xcol 0) x_row x_col x_val)
    (\[0 <= i < N] \*
      harray_int xrow x_row d \* 
      harray_int xcol x_col d \* 
      harray_int xval x_val d)
    (fun hr => 
     \[hr = fun=> List.nth (abs i) xval 0] \* 
      harray_int xrow x_row d \* 
      harray_int xcol x_col d \* 
      harray_int xval x_val d).
Proof.
  rewrite -wp_equiv; xsimpl=> ?.
  xwp; xapp index2.spec=> //.
  xapp; xsimpl*; rewrite -combine_nth; last lia. 
  rewrite index_nodup // combine_length; lia. 
Qed.

Lemma get_spec_out_unary `{Inhab D} (x_row x_col x_val : loc) (i j : int) d : 
  htriple (single d tt) 
    (fun=> get i j x_row x_col x_val)
    (\[~ In (i, j) (combine xrow xcol)] \*
      harray_int xrow x_row d \* 
      harray_int xcol x_col d \* 
      harray_int xval x_val d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      harray_int xrow x_row d \* 
      harray_int xcol x_col d \* 
      harray_int xval x_val d).
Proof.
  rewrite -wp_equiv; xsimpl=> ?.
  xwp; xapp index2.spec=> //.
  xapp; xsimpl*; rewrite memNindex // nth_overflow // combine_length; lia.
Qed.

Lemma get_spec_out `{Inhab D} fs (x_row x_col x_val : loc) : 
  htriple fs
    (fun i => get (eld i).1 (eld i).2 x_row x_col x_val)
    (\[forall d, indom fs d -> ~ In (eld d) (combine xrow xcol)] \*
      (\*_(d <- fs) harray_int xrow x_row d) \* 
      (\*_(d <- fs) harray_int xcol x_col d) \* 
       \*_(d <- fs) harray_int xval x_val d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      (\*_(d <- fs) harray_int xrow x_row d) \*
      (\*_(d <- fs) harray_int xcol x_col d) \*  
       \*_(d <- fs) harray_int xval x_val d).
Proof.
  apply/htriple_val_eq/htriple_conseq;
  [|eauto|move=> ?]; rewrite -hstar_fset_pure -?hbig_fset_hstar; first last.
  { move=> ?; apply: applys_eq_init; reflexivity. }
  apply/htriple_union_pointwise=> [> -> //|[?][??]?]. 
  rewrite -wp_equiv wp_single. 
  xapp get_spec_out_unary=> //= ??->.
  xsimpl*.
Qed.

(* Lemma SumIf {A : Type} {P : A -> Prop} {fs F G} (C : A -> int -> int) : 
  (Σ_(i <- fs) C i (If P i then F i else G i)) = 
  Σ_(i <- fs ∩ P) C i (F i) + Σ_(i <- fs ∖ P) C i (G i).
Proof using.
Admitted. *)

Definition sum := 
  <{
  fun xval =>
  let s = ref 0 in
  for i <- [0, N] {
    let x = xval[i] in 
    s += x
  };
  ! s
}>.

Ltac fold' := 
  rewrite ?label_single ?wp_single
    -/(For_aux _ _) 
    -/(For _ _ _) //=.


Lemma sum_spec `{Inhab D} (x_row x_col x_val : loc) : 
  {{ arr(x_row, xrow)⟨1, (0,0)⟩ \\*
     arr(x_col, xcol)⟨1, (0,0)⟩ \\*
     arr(x_val, xval)⟨1, (0,0)⟩ \\*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_row, xrow)⟨2, i⟩) \\*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_col, xcol)⟨2, i⟩) \\*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_val, xval)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}   => sum x_val];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get ld.1 ld.2 x_row x_col x_val}
  }]
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) hv[`2](i)] \* \Top}}.
Proof with fold'.
  have lE: length (combine xrow xcol) = N :> int by rewrite combine_length; lia.
  xfocus (2,0) (combine xrow xcol).
  rewrite (hbig_fset_part (`[0, Nrow] \x `[0, Ncol]) (combine xrow xcol)). (* TODO: move to xfocus *)
  xapp get_spec_out=> //.
  { case=> ?? /[! @indom_label_eq]-[_]/=. 
    rewrite /intr filter_indom indom_prod; autos*. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); 
  set (H2 := hbig_fset hstar (_ ∖ _) _);
  set (H3 := hbig_fset hstar (_ ∖ _) _).
  xframe (H1 \* H2 \* H3); clear H1 H2 H3.
  xin (1,0) : xwp; xapp=> s...
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ combine xrow xcol = combine xrow xcol.
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

End coo.

End coo.


*)