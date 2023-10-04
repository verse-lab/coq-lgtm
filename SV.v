Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct Unary Loops COO.
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

Definition sorted (l : list int) : Prop. Admitted.
Definition max (l : list int) : int. Admitted.

Definition merge (l1 l2 : list int) : list int. Admitted.

Lemma In_merge l1 l2 x : In x (merge l1 l2) = (In x l1 \/ In x l2).
Proof. Admitted.

Lemma sorted_nodup l : sorted l -> NoDup l.
Admitted.

Lemma sorted_merge l1 l2 : sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Admitted.

Lemma sorted_max_size l i : 
  i + 1 = length l -> l[i] = max l.
Admitted.

Lemma max_sublist l1 l2 : 
  (forall x, In x l1 -> In x l2) -> max l2 >= max l1.
Admitted.

Lemma nth_le_max l i :
  i >= 0 ->
  sorted l ->
  l[i] >= max l -> i + 1 = length l.
Admitted.

Lemma sorted_le i j l :
  sorted l ->
  0 <= i < length l ->
  0 <= j < length l ->
    i < j -> l[i] < l[j].
Admitted.

Lemma max_takeS i l : 
  0 <= i < length l ->
  max (take (abs (i + 1)) l) = Z.max l[i] (max (take (abs i) l)).
Admitted.

Lemma In_lt x i l :
  0 <= i < length l - 1 ->
  sorted l ->
    In x l -> x < l[i+1] -> x <= l[i].
Admitted.

Lemma max_le x l : 
  In x l -> x <= max l.
Proof.
Admitted.

Lemma size_merge l1 l2: 
  length (merge l1 l2) >= Z.max (length l1) (length l2).
Proof.
Admitted.

Lemma max0 : max nil = -1.
Proof.
Admitted.

Lemma In_le_0 l x :
  sorted l -> In x l -> x >= l[0].
Admitted.

End pure_facts.

Module sparse_vec.

(* Module Export AD := WithUnary(IntDom). *)
Import coo_vec.

Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.

Section sparse_vec.

Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.
Notation "'yind'" := ("y_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'yval'" := ("y_val":var) (in custom trm at level 0) : trm_scope.
Notation "'iX'" := ("iX":var) (in custom trm at level 0) : trm_scope.
Notation "'iY'" := ("iY":var) (in custom trm at level 0) : trm_scope.
Notation "'ans'" := ("ans":var) (in custom trm at level 0) : trm_scope.

Import List.

Context (xind xval yind yval : list int).
Context (Nx Ny M : int).
Hypothesis len_xind : length xind = Nx :> int.
Hypothesis len_xval : length xval = Nx :> int.
Hypothesis len_yind : length yind = Ny :> int.
Hypothesis len_yval : length yval = Ny :> int.
Hypothesis sorted_xind : sorted xind.
Hypothesis sorted_yind : sorted yind.
Hypothesis xind_leq : forall x, In x xind -> 0 <= x < M.
Hypothesis yind_leq : forall x, In x yind -> 0 <= x < M.

Notation "'while' C '{' T '}'"  :=
  (While C T)
  (in custom trm at level 69,
    C, T at level 0,
    format "'[' while  C ']'  '{' '/   ' '[' T  '}' ']'") : trm_scope.

Definition dotprod := <{
  fun xind xval yind yval =>
    let ans = ref 0 in
    let iX = ref 0 in 
    let iY = ref 0 in 
      while (
        let "ix" = !iX in
        let "iy" = !iY in
        let "iXl" = "ix" < Nx in 
        let "iYl" = "iy" < Ny in
        "iXl" && "iYl") {
        let "ix" = !iX in
        let "iy" = !iY in
        let "iXind" = xind["ix"] in 
        let "iYind" = yind["iy"] in 
        let "cnd" = "iXind" = "iYind" in 
        if "cnd" then 
          let "iXind" = xval["ix"] in 
          let "iYind" = yval["iy"] in 
          let "val" = "iXind" * "iYind" in
          ans += "val";
          ++iX;
          ++iY
        else 
          let "cnd" = "iXind" < "iYind" in 
          if "cnd" then 
            ++iX 
          else ++iY
      }; !ans
}>.

Hint Rewrite hstar_fset_Lab : hstar_fset.

Definition arr1 x_ind y_ind x_val y_val := arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \*
  arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩.

Ltac fold' := 
  rewrite ?label_single ?wp_single
    -/(While_aux _ _) 
    -/(While _ _) //=.

Notation size := Datatypes.length.

Lemma not_isTrueE (P: Prop) : (~ isTrue P) = ~ P.
Proof.
Admitted.

Ltac bool_rew := 
  rewrite ?false_eq_isTrue_eq ?istrue_isTrue_eq ?true_eq_isTrue_eq -?(isTrue_and, isTrue_not, isTrue_or) ?not_isTrueE.

Lemma val_int_eq i j : 
  (val_int i = val_int j) = (i = j).
Proof. by extens; split=> [[]|]->. Qed.

Transparent take.

Lemma dotprod_spec `{Inhab D} (x_ind x_val y_ind y_val : loc) : 
  {{ arr1 x_ind y_ind x_val y_val \*
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, M]) arr(y_ind, yind)⟨3, i⟩) \\*
     (\*_(i <- `[0, M]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    [1| ld in `{0}   => dotprod x_ind x_val y_ind y_val];
    [2| ld in `[0,M] => get Nx ld x_ind x_val];
    [3| ld in `[0,M] => get Ny ld y_ind y_val]
  }]
  {{ hv, \[hv[`1](0) = Σ_(i <- `[0,M]) (hv[`2](i) * hv[`3](i))] \* \Top}}.
Proof with fold'.
  set (ind := merge xind yind).
  have?: NoDup xind by exact/sorted_nodup.
  have?: NoDup yind by exact/sorted_nodup.
  have?: NoDup ind by exact/sorted_nodup/sorted_merge.
  xfocus (2,0) (ind).
  rewrite {1 2}(hbig_fset_part `[0, M] ind).
  xapp (@get_spec_out xind xval); eauto.
  { case=> ??/=/[!@indom_label_eq]-[_].
    rewrite /intr filter_indom/= /Sum.mem/ind In_merge; autos*. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); 
  set (H2 := hbig_fset hstar (_ ∖ _) _).
  xframe (H1 \* H2); clear H1 H2.
  xfocus (3,0) (ind).
  rewrite (hbig_fset_part `[0, M] ind).
  xapp (@get_spec_out yind yval); eauto.
  { case=> ??/=/[!@indom_label_eq]-[_].
    rewrite /intr filter_indom/= /Sum.mem/ind In_merge; autos*. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); 
  set (H2 := hbig_fset hstar (_ ∖ _) _).
  xframe (H1 \* H2); clear H1 H2.
  set (H1 := _ \* hbig_fset _ _ _); set (H2 := _ \* H1); set (arrs := _ \* H2).
  xin (1,0) : xwp; xapp=> ans; xwp; xapp=> iX; xwp; xapp=> iY...
  have E : `[0,M] ∩ ind = ind.
  { apply/fset_extens=> ?. 
    rewrite /intr filter_indom /ind -fset_of_list_in /Sum.mem ?In_merge; splits*.
    rewrite ?indom_interval=> -[]; autos*. }
  rewrite ?E (fset_of_list_nodup 0) //.
  set (cond ix iy := isTrue (ix < Nx /\ iy < Ny)).
  set (Inv (b : bool) (i : int) := 
    \exists (ix iy : int), 
      iY ~⟨(1, 0)%Z, 0⟩~> iy \* iX ~⟨(1, 0)%Z, 0⟩~> ix \*
      arr1 x_ind y_ind x_val y_val \*
      \[(i = size ind -> ~ b) /\ 0 <= ix /\ 0 <= iy /\
        (i < size ind -> ind[i] > max (take (abs ix) xind)) /\
        (i < size ind -> ind[i] > max (take (abs iy) yind)) /\ 
        b = cond ix iy /\
        (b -> 
          (ind[i] = Z.min xind[ix] yind[iy] /\ 
          (forall x, In x xind -> x < xind[ix] -> x < yind[iy]) /\  
          (forall y, In y yind -> y < yind[iy] -> y < xind[ix])))]).
  set (op hv i := hv[`2](ind[i]) * hv[`3](ind[i])).
  set (R1 i := arr(y_ind, yind)⟨3,i⟩ \* arr(y_val, yval)⟨3,i⟩).
  set (R2 i := arr(x_ind, xind)⟨2,i⟩ \* arr(x_val, xval)⟨2,i⟩).
  eapply xwhile_big_op_lemma2 with 
    (Inv := Inv) (op := op) 
    (R1 := R1) (R2 := R2) 
    (R1' := fun=> \Top) (R2':= fun=> \Top) (p := ans)=> //; try eassumption.
  { move=> l s ?.
    rewrite {1}/Inv; xnsimpl=> ix iy[?][?][?][LM1][LM2][].
    rewrite /cond. bool_rew=> -[??]/(_ eq_refl)-[]indlE[L1 L2].
    rewrite /arr1; clear arrs H1 H2.
    xin (1,0): do 5 (xwp; xapp); xwp; xif=> C.
    { xin (1,0): do 3 (xwp; xapp); xwp; xapp incr.spec; (xwp; xapp incr1.spec); xapp incr1.spec=> ?.
      rewrite /op /=; rewrite <-?hstar_assoc.
      set (Heap := _ \* harray_int xind _ _); rewrite /R2...
      rewrite val_int_eq in C; rewrite {-1 4}indlE -C Z.min_id.
      xin (2,0): fold'; xapp get_spec_in; eauto.
      rewrite /R1 indlE C Z.min_id...
      xapp get_spec_in; eauto.
      rewrite /Heap /Inv /arr1/cond.
      have SlE: l + 1 = size ind -> ~ isTrue (ix + 1 < Nx /\ iy + 1 < Ny). 
      { move: C indlE=>-> /[! Z.min_id]/[swap]/sorted_max_size->; bool_rew.
        have: max ind >= max yind by apply/max_sublist=>?; rewrite In_merge; right.
        move=>/[swap]->/nth_le_max-> //; lia. }
      xsimpl (ix + 1) (iy + 1); splits; [|lia|lia| | |autos*|]...
      { move=> ?; rewrite max_takeS; last lia. 
        suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      { move=> ?; rewrite max_takeS; last lia. 
        suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      bool_rew=> -[]??; splits*.
      { admit. }
      { move=> x ??; move: (@sorted_le iy (iy+1) yind sorted_yind).
        suff: (x <= xind[ix]) by lia.
        apply/In_lt... lia. }
      move=> x ??; move: (@sorted_le ix (ix+1) xind sorted_xind).
      suff: (x <= yind[iy]) by lia.
      apply/In_lt... lia. }
    rewrite /op.
    xin (1,0): xwp; xapp; xwp; xif=> L; xapp incr1.spec=> ?.
    { rewrite /op /=; rewrite <-?hstar_assoc.
      set (Heap := _ \* harray_int yval _ _); rewrite /R2...
      rewrite indlE Z.min_l; last lia.
      xin (2,0): fold'; xapp get_spec_in...
      rewrite /R1; xapp get_spec_out_unary; eauto.
      { move/L2/(_ L); lia. }
      rewrite Z.mul_0_r Z.add_0_r.
      rewrite /Heap /Inv /arr1/cond. 
      xsimpl (ix + 1) (iy); splits; [|lia|lia| | |autos*|].
      { move: indlE=> /[!Z.min_l] //; last lia. 
        move=>/[swap]/sorted_max_size->; bool_rew.
        have: max ind >= max xind by apply/max_sublist=>?; rewrite In_merge; left.
        move=>/[swap]->/nth_le_max-> //; lia. }
      { move=> ?; rewrite max_takeS; last lia. 
        suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      { move=> ?. suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      bool_rew=> -[]??; splits*.
      { admit. }
      { move=> x ??; move: (@sorted_le ix (ix+1) xind sorted_xind)=> ?.
        suff: (x <= xind[ix]) by lia.
        apply/In_lt... lia. }
      move=> ? /L2/[apply].
      move: (@sorted_le ix (ix+1) xind sorted_xind); lia. }
    rewrite /op /=; rewrite <-?hstar_assoc.
    set (Heap := _ \* harray_int yval _ _); rewrite /R1...
    rewrite indlE Z.min_r; last lia.
    xin (3,0): fold'; xapp get_spec_in...
    rewrite /R2; xapp get_spec_out_unary; eauto.
    { move/L1. rewrite val_int_eq in C; lia. }
    rewrite Z.mul_0_l Z.add_0_r.
    rewrite /Heap /Inv /arr1/cond; xsimpl (ix) (iy+1); splits; [|lia|lia| | |autos*|].
    { move: indlE=> /[!Z.min_r] //; last lia. 
      move=>/[swap]/sorted_max_size->; bool_rew.
      have: max ind >= max yind by apply/max_sublist=>?; rewrite In_merge; right.
      move=>/[swap]->/nth_le_max-> //; lia. }
    { move=> ?. suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia.
      exact/sorted_merge. }
    { move=> ?; rewrite max_takeS; last lia. 
      suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia.
      exact/sorted_merge. }
    bool_rew=> -[]??; splits*.
    { admit. }
    { move=> ? /L1/[apply].
      move: (@sorted_le iy (iy+1) yind sorted_yind); lia. }
    rewrite val_int_eq in C.
    move=> x ??; move: (@sorted_le iy (iy+1) yind sorted_yind)=> ?.
    suff: (x <= yind[iy]) by lia.
    apply/In_lt... lia. }
  { move=> l *; rewrite /Inv/op/ntriple.
    xpull=> ix iy []_[]?[]?[]L1[]L2; rewrite /cond; bool_rew=> /[!not_and_eq]-[] []G _.
    { rewrite /R1.
      xin (3,0): fold'; xapp get_spec=> *...
      rewrite /R2.
      xapp get_spec_out_unary...
      { move/max_le; move: L1; rewrite take_ge ?length_List_length; (math||lia). }
      splits*=> //.
      { move=> ?. suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      { move=> ?. suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
        bool_rew; lia. }
    rewrite /R2.
    xin (2,0): fold'; xapp get_spec=> *...
    rewrite /R1.
    xapp get_spec_out_unary...
    { move/max_le; move: L2; rewrite take_ge ?length_List_length; (math||lia). }
    { lia. }
    splits*=> //.
    { move=> ?. suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia.
      exact/sorted_merge. }
    { move=> ?. suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia.
      exact/sorted_merge. }
    bool_rew; lia. }
  { move=> ???. rewrite /ntriple -xnwp1_lemma /=.
    rewrite /Inv; xpull=> ix iy C.
    do ? (xwp; xapp). xapp and.spec=> //.
    by move=> ?->; bool_rew; case: C=> ? [?][?][?][?][]->. }
  { move=> b; rewrite /Inv; xsimpl*=> ?? []/(_ eq_refl); by case: b. }
  { admit. }
  { admit. }
  { admit. }
  { lia. }
  { rewrite /arr1 /Inv/arrs/arr1; xsimpl 0 0.
    { splits; [|lia|lia| | |autos*|].
      { rewrite /cond/ind; bool_rew; move: (size_merge xind yind); lia. }
        { rewrite abs_0 /= max0=> ?.
          have: (In (nth 0 ind 0) ind) by apply/nth_In; lia.
          rewrite In_merge=> -[/xind_leq|/yind_leq]; lia. }
        { rewrite abs_0 /= max0=> ?.
          have: (In (nth 0 ind 0) ind) by apply/nth_In; lia.
          rewrite In_merge=> -[/xind_leq|/yind_leq]; lia. }
        do ? split.
        { admit. }
        { move=> ?/(In_le_0 _ sorted_xind); lia. }
        move=> ?/(In_le_0 _ sorted_yind); lia. }
    rewrite /H2/H1 ?E (fset_of_list_nodup 0) // /R1 /R2.
    rewrite -> ?hbig_fset_hstar; xsimpl*. }
  simpl=> v. xapp; xsimpl; rewrite /op.
Admitted.

End sparse_vec.

End sparse_vec.