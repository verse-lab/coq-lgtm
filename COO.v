Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum ListCommon.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops Unary.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Coercion to_int : val >-> Z.

Module coo_vec.
Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.

Section coo_vec.
Local Notation D := (labeled int).

Implicit Type d : D.


Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.

Import List Vars.

Context (xind xval : list int).
Context (N M : int).
Hypothesis len_xind : length xind = N :> int.
Hypothesis len_xval : length xval = N :> int.
Hypothesis nodup_xind : NoDup xind.
Hypothesis xind_leq : forall x, In x xind -> 0 <= x < M.

Definition indexf := index.func N.

Definition get := 
  <{
  fun i xind xval =>
    let k = indexf i xind in 
    read_array xval k
}>.

Lemma get_spec_in `{Inhab D} (x_ind x_val : loc) i d : 
  htriple (single d tt) 
    (fun=> get (List.nth (abs i) xind 0) x_ind x_val)
    (\[0 <= i < N] \*
      harray_int xind x_ind d \* 
      harray_int xval x_val d)
    (fun hr => 
     \[hr = fun=> List.nth (abs i) xval 0] \* 
      harray_int xind x_ind d \* 
      harray_int xval x_val d).
Proof.
  rewrite -wp_equiv; xsimpl=> ?.
  xwp; xapp (@index.spec _ H)=> //.
  xapp; xsimpl*; rewrite index_nodup //; math.
Qed.

Lemma get_spec_out_unary `{Inhab D} (x_ind x_val : loc) (i : int) d : 
  htriple (single d tt) 
    (fun=> get i x_ind x_val)
    (\[~ In i xind] \*
      harray_int xind x_ind d \* 
      harray_int xval x_val d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      harray_int xind x_ind d \* 
      harray_int xval x_val d).
Proof.
  rewrite -wp_equiv; xsimpl=> ?.
  xwp; xapp (@index.spec _ H)=> //.
  xapp; xsimpl*; rewrite memNindex // nth_overflow //; math.
Qed.


Lemma get_spec_out `{Inhab D} (fs : fset D) (x_ind x_val : loc) : 
  htriple fs
    (fun i => get (eld i) x_ind x_val)
    (\[forall d, indom fs d -> ~ In (eld d) xind] \*
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
  rewrite -wp_equiv wp_single; xapp get_spec_out_unary=> // ??->.
  xsimpl*.
Qed.

Lemma get_spec `{Inhab D} (x_ind x_val : loc) d (l : int): 
  htriple (single d tt) 
    (fun=> get l x_ind x_val)
    (harray_int xind x_ind d \* 
      harray_int xval x_val d)
    (fun hr => 
      harray_int xind x_ind d \* 
      harray_int xval x_val d).
Proof.
  rewrite -wp_equiv; xsimpl.
  xwp; xapp @index.spec=> //.
  xapp; xsimpl*.
Qed.


Definition sum := 
  <{
  fun xind xval =>
  let s = ref 0 in
  for i <- [0, N] {
    let x = read_array xval i in 
    s += x
  };
  ! s
}>.

(* Tactic Notation "xin" constr(S1) ":" tactic(tac) := 
  let n := constr:(S1) in
  xfocus n; tac; try(
  first [xunfocus | xcleanup n]; simpl; try apply xnwp0_lemma). *)

Ltac fold' := 
  rewrite ?label_single ?wp_single
    (* -/(incr _)  *)
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Lemma sum_spec `{Inhab D} (x_ind x_val : loc) : 
  {{ arr(x_ind, xind)⟨1, 0⟩ \*
     arr(x_val, xval)⟨1, 0⟩ \\* 
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) }}
  [{
    [1| ld in `{0}   => sum x_ind x_val];
    [2| ld in `[0,M] => get ld x_ind x_val]
  }]
  {{ hv, \[hv[`1](0) = Σ_(i <- `[0,M]) hv[`2](i)] \* \Top}}.
Proof with fold'.
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus (2,0) xind.
  rewrite (hbig_fset_part `[0, M] xind). (* TODO: move to xfocus *)
  xapp get_spec_out=> //. 1: case=> ??; indomE; autos*.
  xdrain_unused.
  xin (1,0) : xwp; xapp=> s...
  have E : `[0,M] ∩ xind = xind by apply intr_list.
  rewrite E (fset_of_list_nodup 0) // len_xind.
  xfor_sum Inv R (fun=> \Top) (fun hv i => hv[`2](xind[i])) s.
  { (xin (1,0): (xwp; xapp; xapp (@incr.spec _ H)=> y))...
    xapp get_spec_in=> //; xsimpl*. }
  { move=> Neq ???; apply/Neq. 
    move/NoDup_nthZ: nodup_xind; apply; autos*; math. }
  xapp; xsimpl.
  xsum_normalize.
  by rewrite E (SumList 0) // len_xind.
Qed.

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
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus (2,0) xind.
  rewrite (hbig_fset_part `[0, M] xind). (* TODO: move to xfocus *)
  xapp get_spec_out=> //. 1: case=> ??; indomE; autos*.
  xdrain_unused.
  xin (1,0) : xwp; xapp=> s...
  have E : `[0,M] ∩ xind = xind by apply intr_list.
  rewrite E (fset_of_list_nodup 0) // len_xind.
  xfor_sum Inv R (fun=> \Top) (fun hv i => (hv[`2](xind[i]) * dvec[xind[i] ])) s.
  { (xin (1,0): do 4 (xwp; xapp); xapp (@incr.spec _ H)=> y)...
    xapp get_spec_in=> //; xsimpl*. }
  { move=> Neq ???; apply/Neq. 
    move/NoDup_nthZ: nodup_xind; apply; autos*; math. }
  xapp; xsimpl.
  xsum_normalize.
  by rewrite (SumIf (fun=> Z.mul^~ _)) E (SumList 0) // len_xind Sum0s Z.add_0_r.
Qed.

End coo_vec.


End coo_vec.




Module coo. 

Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.


Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Section coo.

Local Notation D := (labeled (int * int)).
Implicit Type d : D.

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
  xwp; xapp (@index2.spec _ H)=> //.
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
  xwp; xapp (@index2.spec _ H)=> //.
  xapp; xsimpl*; rewrite memNindex // nth_overflow // combine_length; lia.
Qed.

Lemma get_spec_out `{Inhab D} (fs : fset D) (x_row x_col x_val : loc) : 
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
  xset_Inv Inv 1; xset_R int Inv R 2.
  have lE: length (combine xrow xcol) = N :> int by rewrite combine_length; lia.
  xfocus (2,0) (combine xrow xcol).
  rewrite (hbig_fset_part (`[0, Nrow] \x `[0, Ncol]) (combine xrow xcol)). (* TODO: move to xfocus *)
  xapp get_spec_out=> //. 1: case=> ??; indomE; autos*.
  xdrain_unused.
  xin (1,0) : xwp; xapp=> s...
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ combine xrow xcol = combine xrow xcol.
  { apply/fset_extens=> -[r c]. specializes xrow_leq r. specializes xcol_leq c. 
    indomE. rewrite -fset_of_list_in /Sum.mem in_combineE /=. tauto. }
  rewrite ?E (fset_of_list_nodup (0,0)) // lE.
  xfor_sum Inv R (fun=> \Top) (fun hv i => hv[`2]((xrow[i], xcol[i]))) s.
  { (xin (1,0): (xwp; xapp; xapp (@incr.spec _ H)=> y))...
    rewrite ?combine_nth /=; try lia.
    xapp get_spec_in=> //; xsimpl*. }
  { move=> Neq ???; apply/Neq. 
    move/NoDup_nthZ: nodup_xrowcol; apply; autos*; math. }
  { rewrite combine_nth //; lia. }
  xapp; xsimpl.
  xsum_normalize.
  rewrite E (SumList (0,0)) // lE. apply SumEq=>*. by rewrite -combine_nth; last lia.
Qed.

End coo.

End coo.


