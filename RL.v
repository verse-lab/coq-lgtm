Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops Unary ListCommon.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Coercion to_int : val >-> Z.

Module runlength.

Module min.
Section min.

Context {D : Type}.

Definition func :=
  <{fun "b" "c" =>
    let "cnd" = "b" < "c" in 
    if "cnd" then "b" else "c"
  }>.

Lemma spec `{Inhab D} (b c : int) d : 
  @htriple D (single d tt) 
    (fun=> func b c)
    \[]
    (fun hr => \[hr = fun d=> Z.min b c]).
Proof.
  xwp;xapp; xwp; xif=> ?; xwp; xval; xsimpl; extens=>?;f_equal; lia.
Qed.
End min.
End min.

Hint Resolve min.spec : lhtriple.

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Notation "'while' C '{' T '}'"  :=
  (While C T)
  (in custom trm at level 69,
    C, T at level 0,
    format "'[' while  C ']'  '{' '/   ' '[' T  '}' ']'") : trm_scope.

Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.
Notation "'yind'" := ("y_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'yval'" := ("y_val":var) (in custom trm at level 0) : trm_scope.

(* FIXME: A possible problem is that search assumes the existence of answer, while index does not;
    this may be bad. 
  As a direct result, only one spec of get is proven. *)

Section runlength.

Import List Vars.

Context (xind xval : list int) {HindIIL : IncreasingIntList xind}.
Hypothesis H_length_xval : length xval = length xind - 1 :> int.

Local Notation D := (labeled int).

Implicit Type d : D.

Section get.

Definition get := 
  <{
  fun i xind xval =>
    let k = search.func i xind in 
    read_array xval k
}>.

Lemma get_spec_unary `{Inhab D} (x_ind x_val : loc) d 
  (k : int) 
  (* (Hk : (0 <= k < xind[(length xind - 1)])) *)
  (a : int) (Ha : (0 <= a < (length xind - 1))) 
  (Hka : (xind[a] <= k < xind[a + 1])) : 
  htriple (single d tt) 
    (fun=> get k x_ind x_val)
    (harray_int xind x_ind d \* 
      harray_int xval x_val d)
    (fun hr => 
      \[hr d = val_int (xval[a])] \*
      harray_int xind x_ind d \* 
      harray_int xval x_val d).
Proof.
  apply wp_equiv.
  pose proof (@IIL_L_bounded_impl _ HindIIL _ eq_refl _ _ Ha Hka) as Hk.
  xwp; xapp (@search.spec); eauto; xapp; xsimpl*.
Qed.

Lemma get_spec (k : int)  (x_ind x_val : loc)
  (fs : fset (labeled int)) :
  0 <= k < length xind - 1 -> 
  (forall i, indom fs i -> xind[k] <= (eld i) < xind[k+1]) ->
    htriple fs
      (fun d => get (eld d) x_ind x_val)
      (\*_(d <- fs) 
          (harray_int xind x_ind d \* 
          harray_int xval x_val d))
      (fun hr => \[hr = fun d => xval[k] ] \*
        \*_(d <- fs) 
          (harray_int xind x_ind d \* 
          harray_int xval x_val d)).
Proof.
  move=> *.
  apply/htriple_val_eq/htriple_conseq;
  [|eauto|move=> ?]; rewrite -?hstar_fset_pure -?hbig_fset_hstar; first last.
  { move=> ?; apply: applys_eq_init; reflexivity. }
  apply/htriple_union_pointwise=> [> -> //|??].
  rewrite -wp_equiv wp_single; xapp @get_spec_unary=> //; eauto=> ?->.
  xsimpl*. 
Qed.

Lemma get_spec_seg `{Inhab D} (x_ind x_val : loc) (k : int) 
  (Hk : 0 <= k < (length xind - 1)) l : 
  htriple (label (Lab l (ind_seg xind k)))
    (fun d => get (eld d) x_ind x_val)
    ((\*_(d0 <- (label (Lab l (ind_seg xind k)))) 
        (harray_int xind x_ind d0 \* 
        harray_int xval x_val d0)))
    (fun hr => 
      (\*_(d0 <- (label (Lab l (ind_seg xind k))))
        \[hr d0 = val_int (xval[k])]) \*
      (\*_(d0 <- (label (Lab l (ind_seg xind k)))) 
        (harray_int xind x_ind d0 \* 
        harray_int xval x_val d0))).
Proof.
  apply/htriple_conseq; [apply/get_spec| |]; eauto.
  { move=> -[>]; indomE=> -[<-]/=. rewrite /ind_seg; by indomE. }
  move=> ?; xsimpl=>->; rewrite hstar_fset_pure; xsimpl*.
Qed.

End get.

Section rlsum.

Variables (M N : int).
Hypotheses (EM : M = length xind - 1) (EN : N = xind[M]).

Definition rlsum :=
  <{ fun xind xval => 
      let s = ref 0 in 
      for i <- [0, M] {
        let "tmp1" = ! s in
        let "tmp2" = read_array xval i in
        let "tmp3" = i + 1 in
        let "tmp4" = read_array xind "tmp3" in
        let "tmp5" = read_array xind i in
        let "tmp6" = "tmp4" - "tmp5" in
        let "tmp7" = "tmp2" * "tmp6" in
        let "tmp8" = "tmp1" + "tmp7" in
        s := "tmp8"
      };
      let "res" = ! s in
      free s; 
      "res"
  }>.

Ltac fold' := 
  rewrite ?label_single ?wp_single
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Lemma rlsum_spec `{Inhab D} (x_ind x_val : loc) : 
  {{ arr(x_ind, xind)⟨1, 0⟩ \*
     arr(x_val, xval)⟨1, 0⟩ \* 
     (\*_(i <- `[0, N]) arr(x_ind, xind)⟨2, i⟩) \*
     (\*_(i <- `[0, N]) arr(x_val, xval)⟨2, i⟩) }}
  [{
    [1| ld in `{0}   => rlsum x_ind x_val];
    [2| ld in `[0,N] => get ld x_ind x_val]
  }]
  {{ hv, \[hv[`1](0) = Σ_(i <- `[0,N]) hv[`2](i)] \* 
      arr(x_ind, xind)⟨1, 0⟩ \*
      arr(x_val, xval)⟨1, 0⟩ \* 
      (\*_(i <- `[0, N]) arr(x_ind, xind)⟨2, i⟩) \*
      (\*_(i <- `[0, N]) arr(x_val, xval)⟨2, i⟩)
  }}.
Proof with fold'.
  xin (1,0) : xwp; xapp=> s...
  rewrite <- interval_segmentation with (L:=xind), <- ! EM; auto.
  2: now subst M N.
  set (R i := arr(x_ind, xind)⟨2, i⟩ \* arr(x_val, xval)⟨2, i⟩ : hhprop D).
  set (Inv (i : int) := arr(x_ind, xind)⟨1, 0⟩ \* arr(x_val, xval)⟨1, 0⟩).
  set (op hv (j : int) := (Σ_(i <- (ind_seg xind j)) hv[`2](i))).
  xfor_sum Inv R R op s.
  2: intros; apply ind_seg_disjoint with (N:=N); subst M N; 
    try math; try autorewrite with indomE; try assumption.
  { (* align *)
    rewrite /Inv /R /op.
    (xin (1,0): (do 9 (xwp; xapp)))...
    subst M.
    xapp (@get_spec_seg H x_ind x_val l0 H0)=> r.
    rewrite hstar_fset_pure.
    xsimpl=> Er.
    (* TODO have no other way? can only touch himpl? *)
    eapply eq_ind_r with (y:=val_int _).
    1: apply himpl_refl.
    do 2 f_equal. 
    erewrite SumEq. 
    2: intros ? HH; specialize (Er _ HH); rewrite Er; reflexivity.
    rewrite SumConst_interval; simpl; try math.
    apply IIL_L_inc'; auto; try math.
  }
  { (* post *)
    xwp. xapp. xwp. xseq. 
    (* TODO conjecture: xapp has bad compatibility with free *)
    (* bad proof start *)
    eapply wp_equiv, htriple_conseq_frame.
    2: apply himpl_refl.
    1: rewrite <- hbig_fset_label_single' with (Q:=fun d0 => s ~(d0)~> _), label_single; apply htriple_free.
    xsimpl.
    (* bad proof end *)
    xwp. xval. xsimpl. f_equal.
    rewrite SumCascade; try reflexivity.
    intros i0 j0 Hneq Hi0 Hj0. subst M N.
    eapply ind_seg_disjoint.
    rewrite indom_interval in Hi0, Hj0. 2: reflexivity. all: auto.
  }
Qed.

End rlsum.

End runlength.

Section alpha_blending.

Import List.

Context (xind xval : list int) {HindIIL : IncreasingIntList xind}.
Hypothesis H_length_xval : length xval = length xind - 1 :> int.

Context (yind yval : list int) {HindIIL' : IncreasingIntList yind}.
Hypothesis H_length_yval : length yval = length yind - 1 :> int.

Context (Mx My N : int).
Hypotheses (EMx : Mx = length xind - 1) (ENx : N = xind[Mx]).
Hypotheses (EMy : My = length yind - 1) (ENy : N = yind[My]).
Hypotheses (xind0 : xind[0] = 0) (yind0 : yind[0] = 0).

Context (α β : int).

Notation "t1 && t2" :=
  (and.func t1 t2)
  (in custom trm at level 58) : trm_scope.

Hint Resolve and.spec : htriple.

Notation "'i'"     := ("i":var) (in custom trm at level 0) : trm_scope.
Notation "'iX'"     := ("iX":var) (in custom trm at level 0) : trm_scope.
Notation "'iY'"     := ("iY":var) (in custom trm at level 0) : trm_scope.
Notation "'iXl'"    := ("iXl":var) (in custom trm at level 0) : trm_scope.
Notation "'iYl'"    := ("iYl"   :var) (in custom trm at level 0) : trm_scope.
Notation "'ix'"     := ("ix"    :var) (in custom trm at level 0) : trm_scope.
Notation "'iy'"     := ("iy"    :var) (in custom trm at level 0) : trm_scope.
Notation "'ans'"    := ("ans"   :var) (in custom trm at level 0) : trm_scope.
Notation "'step'"   := ("step"  :var) (in custom trm at level 0) : trm_scope.
Notation "'stride'" := ("stride":var) (in custom trm at level 0) : trm_scope.
Notation "'xindx'"  := ("x_indx":var) (in custom trm at level 0) : trm_scope.
Notation "'xvalx'"  := ("x_valx":var) (in custom trm at level 0) : trm_scope.
Notation "'yindy'"  := ("y_indy":var) (in custom trm at level 0) : trm_scope.
Notation "'yvaly'"  := ("y_valy":var) (in custom trm at level 0) : trm_scope.
Notation "'cnd'"    := ("cnd"   :var) (in custom trm at level 0)  : trm_scope.
Notation "'delta'"  := ("delta" :var) (in custom trm at level 0) : trm_scope.

Definition alpha_blend := <{
  fun xind yind xval yval  =>
    let ans    = ref 0 in
    let iX     = ref 0 in
    let iY     = ref 0 in
    let step   = ref 0 in 
      while (
        let step = !step in 
        step < N) {
        let ix = !iX in 
        let iy = !iY in 
        let xindx = xind[ix] in 
        let yindy = yind[iy] in 
        let "st" = !step in
        let cnd = xindx = yindy in 
          (if cnd then 
            let xvalx = xval[ix] in 
            let xvalx = α * xvalx in 
            let yvaly = yval[iy] in 
            let yvaly = β * yvaly in 
            let xvalx = xvalx + yvaly in 
            ++iX;
            ++iY;
            let ix = !iX in 
            let iy = !iY in 
            let xindx = xind[ix] in 
            let yindy = yind[iy] in 
            let stride = min.func xindx yindy in 
            let delta = stride - "st" in 
            let xvalx = xvalx * delta in
              ans += xvalx;
              step := stride
          else 
            let cnd = xindx < yindy in 
            if cnd then 
              let iy = iy - 1 in
              let xvalx = xval[ix] in 
              let xvalx = α * xvalx in 
              let yvaly = yval[iy] in 
              let yvaly = β * yvaly in 
              let xvalx = xvalx + yvaly in 
              ++iX;
              let ix = !iX in 
              let xindx = xind[ix] in 
              let stride = min.func xindx yindy in 
              let delta = stride - "st" in 
              let xvalx = xvalx * delta in
                ans += xvalx;
                step := stride
            else 
              let ix = ix - 1 in
              let xvalx = xval[ix] in 
              let xvalx = α * xvalx in 
              let yvaly = yval[iy] in 
              let yvaly = β * yvaly in 
              let xvalx = xvalx + yvaly in 
              ++iY;
              let iy = !iY in 
              let yindy = yind[iy] in 
              let stride = min.func xindx yindy in 
              let delta = stride - "st" in 
              let xvalx = xvalx * delta in
                ans += xvalx;
                step := stride)
      }; !ans
}>.

Lemma lhtriple_free D : forall (p : loc) (v : val) fs,
  @htriple D fs (fun d => val_free p)
    (\*_(d <- fs) p ~(d)~> v)
    (fun _ => \[]).
Proof using. intros. apply htriple_free. Qed.

Hint Resolve lhtriple_free : lhtriple.

Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.

Lemma val_int_eq i j : 
  (val_int i = val_int j) = (i = j).
Proof. by extens; split=> [[]|]->. Qed.

Ltac fold' := 
  rewrite ?label_single ?wp_single ?val_int_eq
    -/(While_aux _ _) 
    -/(While _ _) //=; try lia.

Ltac abbrv :=
  match goal with 
  | |- context [ While ?c ?f ] => set (cnd := c); set (bdy := f)
  end.

Lemma not_isTrueE (P: Prop) : (~ isTrue P) = ~ P.
Proof.
Admitted.

Ltac bool_rew := 
  rewrite ?false_eq_isTrue_eq ?istrue_isTrue_eq 
    ?true_eq_isTrue_eq -?(isTrue_and, isTrue_not, isTrue_or) ?not_isTrueE.

Notation size := Datatypes.length.

Lemma alpha_blend_spec `{Inhab (labeled int)} (x_ind x_val y_ind y_val : loc) : 
  {{ (arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \*
     arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩) \*
     (\*_(i <- `[0, N]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, N]) arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, N]) arr(y_ind, yind)⟨3, i⟩) \\*
     (\*_(i <- `[0, N]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    {1| ld in `{0}   => alpha_blend x_ind y_ind x_val y_val};
    {2| ld in `[0,N] => get ld x_ind x_val};
    {3| ld in `[0,N] => get ld y_ind y_val}
  }]
  {{ hv, \[hv[`1](0) = Σ_(i <- `[0,N]) (α * hv[`2](i) + β * hv[`3](i))] 
      \* \Top}}.
Proof with (fold'; try abbrv).
  set (ind := merge xind yind).
  have sxind: sorted xind by exact/IIL_sorted. 
  have yxind: sorted yind by exact/IIL_sorted.
  have?: NoDup xind by exact/sorted_nodup. 
  have?: NoDup yind by exact/sorted_nodup.
  have sind: sorted ind by exact/sorted_merge.
  have ndind: NoDup ind by exact/sorted_nodup.
  xin (1,0): (xwp;xapp=> ans); (xwp;xapp=> iX); 
    (xwp;xapp=> iY); (xwp;xapp=> step)...
  have maxindE: max ind = N.
  { move: (max_merge sxind yxind)->.
    rewrite -(sorted_max_size _ Mx) -?(sorted_max_size _ My)... }
  rewrite (@interval_unionE ind)=> //.
  set (Inv (b : bool) (i : int) := 
    arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \\*
    arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩ \\*
    step ~⟨(1,0)%Z,0⟩~> ind[i] \\*
    \exists (ix iy : int), 
      iX ~⟨(1,0)%Z,0⟩~> ix \* iY ~⟨(1,0)%Z,0⟩~> iy \\*
      \[0 <= ix < Mx + 1 /\ 0 <= iy < My + 1 /\ b = isTrue (ind[i] < N) /\ 
        (b -> 
          (ix > 0 -> xind[ix -1] < yind[iy]) /\ 
          (iy > 0 -> yind[iy -1] < xind[ix]) /\
          (ind[i] = Z.min xind[ix] yind[iy]))]).
  set (op hv i := Σ_(i <- `[ind[i], ind[i+1] ]) (α * hv[`2](i) + β * hv[`3](i))).
  set (R3 (i : int) := arr(y_ind, yind)⟨3,i⟩ \* arr(y_val, yval)⟨3,i⟩).
  set (R2 (i : int) := arr(x_ind, xind)⟨2,i⟩ \* arr(x_val, xval)⟨2,i⟩).
  have?: forall i j, i <> j -> 0 <= i < size ind - 1 ->
    0 <= j < size ind - 1 ->
    ind[i + 1] <= ind[j] \/
    ind[j + 1] <= ind[i] \/ ind[i + 1] <= ind[i] \/ ind[j + 1] <= ind[j].
  { move=> i j *. 
    suff: (i+1 <= j -> ind[i+1] <= ind [j]) /\ 
          (j+1 <= i -> ind[j+1] <= ind [i]) by lia.
    split; apply/sorted_leq... }
  xwhile_sum Inv R2 R3 R2 R3 op ans=> //; autos*; try clear bdy cnd.
  { move=> l ??; rewrite /Inv; xnsimpl=> ix iy.
    bool_rew=> -[?][?][indL]/(_ eq_refl)-[ix0][iy0]indE.
    rewrite {}/bdy.
    xfocus (1,0). 
    do 6 (xwp; xapp). xwp; xif=> C.
    { do 5 (xwp; xapp).
      do 2 (xwp; xapp @incr1.spec).
      do ? (xwp; xapp). xwp; xapp @min.spec. do ? (xwp; xapp).
      xwp; xapp @incr.spec; xwp; xapp. 
      xcleanup (1,0); rewrite /op /=.
      rewrite val_int_eq in C.
      move: (indL); rewrite {1}indE {1}ENx -{1}C Z.min_id.
      move/(sorted_le_rev sxind)=> ?.
      move: (indL); rewrite {1}indE {1}ENy {1}C Z.min_id.
      move/(sorted_le_rev yxind)=> ?.
      have indlE: ind[l+1] = Z.min xind[ix + 1] yind[iy + 1].
      { rewrite merge_nthS -/ind ?indE...
        rewrite -{1}C Z.min_id {2}C Z.min_id ?search_nth... }
      rewrite /R2/R3.
      xin (2,0): xapp (@get_spec xind xval HindIIL ix)...
      { move=> [>]; indomE=>-[?]/=; lia. }
      xapp (@get_spec yind yval HindIIL' iy)...
      { move=> [>]; indomE=>-[?]/=; lia. }
      xsimpl (isTrue (ind[l + 1] < N)).
      { splits... move=> ?; splits*=> _.
        { replace (ix +1 -1) with ix by lia; rewrite C. 
          apply/sorted_le... }
        replace (iy +1 -1) with iy by lia; rewrite -C. 
        apply/sorted_le... }
      rewrite SumConst_interval indlE; try xsimpl.
      rewrite -indlE; apply/Z.lt_le_incl/sorted_le... }
    xwp; xapp; xwp; xif=> C'.
    { do 6 (xwp; xapp); xwp; xapp @incr1.spec. 
      do 2 (xwp; xapp); xwp; xapp @min.spec.
      do 2 (xwp; xapp); xwp; xapp @incr.spec; xwp; xapp.
      xcleanup (1,0); rewrite /op /=.
      move: (indL); rewrite {1}indE {1}ENx Z.min_l...
      move/(sorted_le_rev sxind)=> ?.
      have?: (0 < iy).
      { apply/(sorted_le_rev yxind)...
        suff: xind[ix] >= 0 by lia. exact/IILG0. } 
      have indlE: ind[l+1] = Z.min xind[ix + 1] yind[iy].
      { rewrite merge_nthS -/ind ?indE...
        rewrite (Z.min_l xind[ix]) ?search_nth...
        rewrite (@search_nth_pred _ iy)... }
      rewrite /R2/R3.
      xin (2,0): xapp (@get_spec xind xval HindIIL ix)...
      { move=> [>]; indomE=>-[?]/=; lia. }
      xapp (@get_spec yind yval HindIIL' (iy-1))...
      { move=> [>]; indomE=>-[?]/=;
        replace (iy - 1 + 1) with iy; lia. }
      xsimpl (isTrue (ind[l + 1] < N)).
      { splits... move=> ?; splits*.
        { replace (ix + 1 - 1) with ix; lia. }
        suff: xind[ix] < xind[ix + 1] by lia. 
        apply/(sorted_le sxind)... }
      rewrite SumConst_interval indlE; try xsimpl.
      rewrite -indlE; apply/Z.lt_le_incl/sorted_le... }
    do 6 (xwp; xapp); xwp; xapp @incr1.spec. 
    do 2 (xwp; xapp); xwp; xapp @min.spec.
    do 2 (xwp; xapp); xwp; xapp @incr.spec; xwp; xapp.
    xcleanup (1,0); rewrite /op /=.
    rewrite val_int_eq in C.
    move: (indL); rewrite {1}indE {1}ENy Z.min_r...
    move/(sorted_le_rev yxind)=> ?.
    have?: (0 < ix).
    { apply/(sorted_le_rev sxind)...
      suff: yind[iy] >= 0 by lia. exact/IILG0. } 
    have indlE: ind[l+1] = Z.min xind[ix] yind[iy + 1].
    { rewrite merge_nthS -/ind ?indE...
      rewrite (Z.min_r xind[ix]) ?search_nth...
      rewrite (@search_nth_pred _ ix)... }
    rewrite /R2/R3.
    xin (2,0): xapp (@get_spec xind xval HindIIL (ix-1))...
    { move=> [>]; indomE=>-[?]/=;
      replace (ix - 1 + 1) with ix; lia. }
    xapp (@get_spec yind yval HindIIL' iy)...
    { move=> [>]; indomE=>-[?]/=; lia. }
    xsimpl (isTrue (ind[l + 1] < N)).
    { splits... move=> ?; splits*.
      { suff: yind[iy] < yind[iy + 1] by lia. 
        apply/(sorted_le yxind)... }
      replace (iy + 1 - 1) with iy; lia. }
    rewrite SumConst_interval indlE; try xsimpl.
    rewrite -indlE; apply/Z.lt_le_incl/sorted_le... }
  { move=> l _ ?; rewrite /Inv; xnsimpl.
    move=> ?? [?][?][]; bool_rew=> ?.
    suff: (l + 1 = size ind) by lia. 
    apply/sorted_max_le... }
  { move=> ???; rewrite /Inv{}/cnd.
    xnsimpl=> *; xin (1,0): do ? (xwp; xapp).
    xsimpl*. apply/eq_sym/f_equal. autos*. }
  { move=> ??[?][?][->]*; apply/isTrue_eq_false...
    rewrite sorted_max_size... }
  { rewrite /ind; move: (size_merge xind yind)... }
  { rewrite /Inv/R2/R3 merge_nth0 ?xind0 ?yind0 ?Z.min_id...
    rewrite -> ?hbig_fset_hstar; xsimpl.
    splits*... }
  simpl=> ?; rewrite /Inv /op; xsimpl=> *; xwp; xapp; xsimpl.
  rewrite -SumCascade //; disjointE; autos*.
Qed.

End alpha_blending.


End runlength.
