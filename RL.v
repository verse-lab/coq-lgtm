Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct Unary Loops.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Definition to_int (v : val) : int := 
  match v with 
  | val_int i => i 
  | _ => 0
  end.

Coercion to_int : val >-> Z.

(* FILLINHERE *)

Section pure_facts.

(* FILLINHERE *)

End pure_facts.

Module runlength.

(* FIXME: A possible problem is that search assumes the existence of answer, while index does not;
    this may be bad. 
  As a direct result, only one spec of rli is proven. *)

Section runlength.

Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.

Import List Vars.

Context (xind xval : list int) {HindIIL : IncreasingIntList xind}.
Hypothesis H_length_xval : length xval = length xind - 1 :> int.
Hypothesis H_xval_notnil : 0 < length xval.

Section rli.

Definition rli := 
  <{
  fun i xind xval =>
    let k = search.func i xind in 
    read_array xval k
}>.

Lemma rli_spec_unary `{Inhab D} (x_ind x_val : loc) d 
  (k : int) (Hk : (0 <= k < List.nth (abs (length xind - 1)) xind 0))
  (a : int) (Ha : (0 <= a < (length xind - 1))) 
  (Hka : (List.nth (abs a) xind 0 <= k < List.nth (abs (a + 1)) xind 0)) : 
  htriple (single d tt) 
    (fun=> rli k x_ind x_val)
    (harray_int xind x_ind d \* 
      harray_int xval x_val d)
    (fun hr => 
      \[hr d = val_int (List.nth (abs a) xval 0)] \*
      harray_int xind x_ind d \* 
      harray_int xval x_val d).
Proof.
  apply wp_equiv.
  xwp. xapp (@search.spec xind HindIIL H d x_ind k Hk a Ha Hka). (* FIXME: put all these into precondition *)
  intros r Er.
  rewrite wp_single Er. (* TODO why need wp_single here? *)
  xapp; xsimpl*.
Qed.

End rli.

Section rlsum_loopbody.

Definition rlsum_loopbody (real_x_ind real_x_val real_s real_i : trm) :=
  <{  let "tmp1" = ! real_s in
      let "tmp2" = read_array real_x_val real_i in
      let "tmp3" = real_i + 1 in
      let "tmp4" = read_array real_x_ind "tmp3" in
      let "tmp5" = read_array real_x_ind real_i in
      let "tmp6" = "tmp4" - "tmp5" in
      let "tmp7" = "tmp2" * "tmp6" in
      let "tmp8" = "tmp1" + "tmp7" in
      real_s := "tmp8" }>.

Lemma rlsum_loopbody_spec `{Inhab D} d M (x : int) (x_ind x_val : loc) (ps0 : loc) (l : int) (Hl : (0 <= l < M)) :
  htriple (single d tt) 
    (fun=> rlsum_loopbody x_ind x_val ps0 l)
    (ps0 ~(d)~> x \* 
      harray_int xind x_ind d \* 
      harray_int xval x_val d)
    (fun=> 
      ps0 ~(d)~> (x + ((List.nth (abs l) xval 0) * ((List.nth (abs (l+1)) xind 0) - (List.nth (abs l) xind 0)))) \* 
      harray_int xind x_ind d \* 
      harray_int xval x_val d).
Proof.
  unfold rlsum_loopbody. apply wp_equiv. 
  do 9 (xwp; xapp). xsimpl*.
Qed.

End rlsum_loopbody.

Section rlsum_rli.

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Definition rlsum (M : int) :=
  let loopbody := rlsum_loopbody "x_ind" "x_val" "s" "i" in
  let loop := For 0 M (trm_fun "i" loopbody) in
  <{ fun xind xval => 
      let s = ref 0 in 
      for i <- [0, N] {
        loopbody := rlsum_loopbody "x_ind" "x_val" "s" "i"
      };
      let "res" = ! s in
      free s; 
      "res"
  }>.

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
  xfocus (2,0) xind.
  rewrite (hbig_fset_part `[0, M] xind). (* TODO: move to xfocus *)
  xapp get_spec_out=> //.
  { case=> ?? /[! @indom_label_eq]-[_]/=; rewrite /intr filter_indom; autos*. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); set (H2 := hbig_fset hstar (_ ∖ _) _).
  xframe (H1 \* H2); clear H1 H2.
  xin (1,0) : xwp; xapp=> s...
  have E : `[0,M] ∩ xind = xind.
  { apply/fset_extens=> x; rewrite /intr filter_indom -fset_of_list_in; splits*.
    move=> ?; splits*; rewrite* indom_interval. }
  rewrite E fset_of_list_nodup // len_xind.
  set (R i := arr(x_ind, xind)⟨2, i⟩ \* arr(x_val, xval)⟨2, i⟩).
  set (Inv (i : int) := arr(x_ind, xind)⟨1, 0⟩ \* arr(x_val, xval)⟨1, 0⟩).
  xfor_sum Inv R (fun=> \Top) (fun hv i => hv[`2](xind[i])) s.
  { rewrite /Inv. 
    (xin (1,0): (xwp; xapp; xapp incr.spec=> y))...
    xapp get_spec_in=> //; xsimpl*. }
  { move=> Neq ???; apply/Neq. 
    move/NoDup_nthZ: nodup_xind; apply; autos*; math. }
  { rewrite -len_xind; math. }
  xapp; xsimpl.
  under (@SumEq _ _ `[0,M]).
  { move=>*; rewrite to_int_if; over. }
  rewrite SumIf E SumList // len_xind Sum0s; math.
Qed.

End rlsum_rli.
  
End runlength.

End runlength.
