Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Unary_IndexWithBounds.
From SLF Require Import Struct Loops SV2 Subst NTriple Loops2 Struct2 CSR.
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
  apply (Unary.memNindex 0) in Hnotin.
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

Lemma in_interval_list {A : Type} (l : list A) lb rb x: 
   In x (list_interval lb rb l) -> In x l.
Proof.
Admitted.

(* TODO make a local copy here since the one in SV2 depends on many section hypotheses
    (adding "Proof using." may work, though); but in the future, 
    we eventually need to move this to some place which holds all lemmas about fset_of_list *)
Fact intr_list (a b : int) (l: list int) : 
  (forall x, In x l -> a <= x < b) ->
  `[a, b] ∩ l = l.
Admitted.

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

Hint Rewrite @filter_indom : indomE.
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
  xfocus (2,0) (indom (midx \x `[0, Ncol])).
  (* now xapp can no longer handle so many conjunctions; some tweak is needed *)
  rewrite (hbig_fset_part (`[0, Nrow] \x `[0, Ncol]) (indom (midx \x `[0, Ncol]))). (* TODO: move to xfocus *)
  xapp get_spec_out=> [[?][>]|].
  { rewrite /(_ ∖ _). do ? indomE=> //=; autos*. }
  repeat (set (HHQ := hbig_fset hstar (_ ∖ _) _); xframe HHQ; clear HHQ).
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  xin (1,0) : xwp; xapp=> s...
  rewrite -?hbig_fset_hstar.
  match goal with 
    |- context [(_ \* ?a \* ?b \* ?c \* ?d \* (hbig_fset _ _ ?f))] => 
      pose (Inv (i : int) := a \* b \* c \* d); pose (R := f) 
  end. (* smart!! *)
  xfor_sum Inv R R (fun hv i => Σ_(j <- `{midx[i]} \x `[0, Ncol]) hv[`2](j)) s.
  { rewrite /Inv /R.
    xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xsubst (snd : _ -> int).
    xfocus (2,0); rewrite -> ! hbig_fset_hstar.
    xwp; xapp (@Unary.index.Spec `[0, Ncol] Nidx (2,0) midx x_midx (fun=> midx[l0]))=> //.
    rewrite Unary.index_nodup //; try math.
    xwp; xapp. xwp; xif=> ?; [ | math ].
    (* TODO raw xapp will fail here. guess the reason is that it cannot switch between different doms? *)
    (* Yes, just add Inhab (labeled int) as a hypothesis  *)
    do 3 (xwp; xapp).
    xunfocus; xin (1,0) : idtac. (* reformat *)
    xnapp sv.sum_spec...
    { move=> ?/in_interval_list... }
    move=> ?; rewrite -wp_equiv. xsimpl=>->.
    xapp @incr.spec. rewrite csr.sum_prod1E. xsimpl. }
  { left=> /(NoDup_nth _ _).1 Eq; have: abs i0 <> abs j0 by lia. 
    rewrite 1?Eq //; lia. }
  xwp; xapp. xsimpl*. 
  f_equal; under (@SumEq _ _ _ (`[0, Nrow] \x `[0, Ncol])).
  { move=>*; rewrite to_int_if; over. }
  rewrite Sum.SumIf Sum0s Z.add_0_r SumCascade.
  1: rewrite -prod_Union_distr -len_midx -(fset_of_list_nodup 0) ?E //.
  disjointE.
  (* repeating proof *)
  left=> /(NoDup_nth _ _).1 Eq; have: abs i0 <> abs j0 by lia. 
  rewrite 1?Eq //; lia.
Qed.


End unordered_csr.

End unordered_csr.
