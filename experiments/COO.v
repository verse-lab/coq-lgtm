Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibListExt LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibHypHeap LibWP LibXWP LibSepSimpl LibArray LibLoops NTriple.
From LGTM.experiments Require Import Prelude UnaryCommon.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Module coo. 

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

(* Accessor function for sparse COO matrix. COO format consists of three arrays:
  1. xrow -- contains row coordinats of non-zero vaules
  2. xcol -- contains column coordinats of non-zero vaules
  3. xval -- contains vaules of non-zero vaules
  to access an element with `i` and `j` coordintes, we call `index2 i j xrow xcol` function.
  Which essentially is equal to `index (i, j) (zip xrow xcol)` *)
Definition get := 
  <{
  fun i j xrow xcol xval =>
    let k = indexf i j xrow xcol in 
    xval[k]
}>.

Lemma get_spec_in `{Inhab D} (x_row x_col x_val : loc) i d : 
  htriple (`{d}) 
    (fun=> get (xrow[i]) (xcol[i]) x_row x_col x_val)
    (\[0 <= i < N] \*
      arr(x_row, xrow)⟨`d⟩ \* 
      arr(x_col, xcol)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩)
    (fun hr => 
      \[hr = fun=> xval[i] ] \* 
      arr(x_row, xrow)⟨`d⟩ \* 
      arr(x_col, xcol)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩).
Proof.
  xwp; xsimpl=> ?; xapp (@index2.spec _ H)=> //.
  xapp; xsimpl*; rewrite -combine_nth; last lia. 
  rewrite index_nodup // combine_length; lia. 
Qed.

Lemma get_spec_out_unary `{Inhab D} (x_row x_col x_val : loc) (i j : int) d : 
  htriple (`{d}) 
    (fun=> get i j x_row x_col x_val)
    (\[~ In (i, j) (combine xrow xcol)] \*
      arr(x_row, xrow)⟨`d⟩ \* 
      arr(x_col, xcol)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩)
    (fun hr => 
     \[hr = fun=> 0] \* 
      arr(x_row, xrow)⟨`d⟩ \* 
      arr(x_col, xcol)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩).
Proof.
  xwp; xsimpl=> ?; xapp (@index2.spec _ H)=> //.
  xapp; xsimpl*; rewrite memNindex // nth_overflow // combine_length; lia.
Qed.

Lemma get_spec_out `{Inhab D} (fs : fset D) (x_row x_col x_val : loc) : 
  htriple fs
    (fun i => get (eld i).1 (eld i).2 x_row x_col x_val)
    (\[forall d, indom fs d -> ~ In (eld d) (combine xrow xcol)] \*
      (\*_(d <- fs) arr(x_row, xrow)⟨`d⟩) \* 
      (\*_(d <- fs) arr(x_col, xcol)⟨`d⟩) \* 
       \*_(d <- fs) arr(x_val, xval)⟨`d⟩)
    (fun hr => 
     \[hr = fun=> 0] \* 
      (\*_(d <- fs) arr(x_row, xrow)⟨`d⟩) \*
      (\*_(d <- fs) arr(x_col, xcol)⟨`d⟩) \*  
       \*_(d <- fs) arr(x_val, xval)⟨`d⟩).
Proof. xpointwise_build get_spec_out_unary. now destruct (eld _). Qed.

(* #4 from the table
  Summation of all elements in sparse COO matrix *)
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

(* Specification for `sum` *)
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
  xfocus* 2 (combine xrow xcol).
  xapp get_spec_out=> //. 1: case=> ??; indomE; autos*.
  xclean_heap.
  xin 1 : xwp; xapp=> s...
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ combine xrow xcol = combine xrow xcol.
  { apply/fset_extens=> -[r c]. specializes xrow_leq r. specializes xcol_leq c. 
    indomE. rewrite /LibSummation.mem /=. split; try tauto. intros HH. pose proof HH as HH2%in_combineE. tauto. }
  rewrite ?E (fset_of_list_nodup (0,0)) // lE.
  xfor_sum Inv R (fun=> \Top) (fun hv i => hv[`2]((xrow[i], xcol[i]))) s.
  { (xin 1: (xstep; xapp (@incr.spec _ H)=> y))...
    rewrite ?combine_nth /=; try lia.
    xapp get_spec_in=> //; xsimpl*. }
  { move=>Ha Hb Hc; move: Ha; apply contrapose, NoDup_nthZ; autos*; math. }
  { rewrite combine_nth //; lia. }
  xapp; xsimpl.
  xsum_normalize.
  rewrite E (SumList (0,0)) // lE. apply SumEq=>*. by rewrite -combine_nth; last lia.
Qed.

End coo.

End coo.


