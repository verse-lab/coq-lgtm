Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops Unary ListCommon.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

(* TODO possibly, move to_int to some common place *)
Definition to_int (v : val) : int := 
  match v with 
  | val_int i => i 
  | _ => 0
  end.

Coercion to_int : val >-> Z.

Module runlength.

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
Hypothesis H_xval_notnil : 0 < length xval.

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
  xwp. xapp (@search.spec xind _ HindIIL H d x_ind k Hk a Ha Hka). (* FIXME: put all these into precondition *)
  intros r Er.
  rewrite wp_single Er. (* TODO why need wp_single here? *)
  xapp; xsimpl*.
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
  eapply htriple_conseq.
  1: apply htriple_union_pointwise with (Q:=fun d hv => 
        \[hv d = val_int (xval[k])] \*
        harray_int xind x_ind d \* harray_int xval x_val d).
  3: xsimpl.
  1: intros ??? HH; rewrite HH; xsimpl*.
  2:{ xsimpl. intros hv. rewrite -> ! hbig_fset_hstar. xsimpl. }
  (* TODO this is slightly bad rewriting! *)
  intros (ll, d) Hin.
  rewrite indom_label_eq /ind_seg indom_interval in Hin. destruct Hin as (<- & Hin).
  rewrite -wp_equiv wp_single. 
  simpl.
  xapp (@get_spec_unary H x_ind x_val (Lab l d) d k Hk Hin)=> r Er.
  rewrite Er.
  xsimpl*.
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
Hypothesis H_xval_notnil : 0 < length xval.

Context (yind yval : list int) {HindIIL' : IncreasingIntList yind}.
Hypothesis H_length_yval : length yval = length yind - 1 :> int.
Hypothesis H_yval_notnil : 0 < length yval.

Context (Mx My N : int).
Hypotheses (EMx : Mx = length xind - 1) (ENx : N = xind[Mx]).
Hypotheses (EMy : My = length yind - 1) (ENy : N = yind[My]).
Hypotheses (xind0 : xind[0] = 0) (yind0 : yind[0] = 0).

Context (α β : int).

Notation "'i'"     := ("i":var) (in custom trm at level 0) : trm_scope.
Notation "'iX'"     := ("iX":var) (in custom trm at level 0) : trm_scope.
Notation "'iY'"     := ("iY":var) (in custom trm at level 0) : trm_scope.
Notation "'iXl'"    := ("iXl":var) (in custom trm at level 0) : trm_scope.
Notation "'iYl'"    := ("iYl":var) (in custom trm at level 0) : trm_scope.
Notation "'ix'"     := ("ix":var) (in custom trm at level 0) : trm_scope.
Notation "'iy'"     := ("iy":var) (in custom trm at level 0) : trm_scope.
Notation "'ans'"    := ("ans":var) (in custom trm at level 0) : trm_scope.
Notation "'step'"   := ("step":var) (in custom trm at level 0) : trm_scope.
Notation "'stride'" := ("stride":var) (in custom trm at level 0) : trm_scope.
Notation "'xindx'" := ("x_indx":var) (in custom trm at level 0) : trm_scope.
Notation "'xvalx'" := ("x_valx":var) (in custom trm at level 0) : trm_scope.
Notation "'yindy'" := ("y_indy":var) (in custom trm at level 0) : trm_scope.
Notation "'yvaly'" := ("y_valy":var) (in custom trm at level 0) : trm_scope.
Notation "'cnd'"    := ("cnd":var) (in custom trm at level 0) : trm_scope.
Notation "'delta'"    := ("delta":var) (in custom trm at level 0) : trm_scope.

Definition alpha_blend := <{
  fun xind yind xval yval  =>
    let ans    = ref 0 in
    let iX     = ref 1 in
    let iY     = ref 1 in
    let step   = ref 0 in 
    let stride = ref 0 in 
      while (
        let step = !step in 
        step < N) {
        let ix = !iX in 
        let iy = !iY in 
        let xindx = xind[ix] in 
        let yindy = yind[iy] in 
        let cnd = xindx = yindy in 
          (if cnd then 
            stride := xindx;
            ++iX;
            ++iY;
            let step = !step in 
            let stride = !stride in 
            let delta = stride - step in 
            let xvalx = xval[i] in 
            let xvalx = α * xvalx in 
            let yvaly = yval[i] in 
            let yvaly = β * yvaly in 
            let xvalx = xvalx + yvaly in 
            let xvalx = xvalx * delta in
              ans += xvalx
          else 
            let cnd = xindx < yindy in 
            if cnd then 
              stride := xindx;
              ++iX;
              let step = !step in 
              let stride = !stride in 
              let delta = stride - step in 
              let xvalx = xval[i] in 
              let xvalx = α * xvalx in 
              let yvaly = yval[i] in 
              let yvaly = β * yvaly in 
              let xvalx = xvalx + yvaly in 
              let xvalx = xvalx * delta in
                ans += xvalx
            else 
              stride := yindy;
              ++iY;
              let step = !step in 
              let stride = !stride in 
              let delta = stride - step in 
              let xvalx = xval[i] in 
              let xvalx = α * xvalx in 
              let yvaly = yval[i] in 
              let yvaly = β * yvaly in 
              let xvalx = xvalx + yvaly in 
              let xvalx = xvalx * delta in
                ans += xvalx);
          let stride = !stride in
          step := stride
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
Proof with fold'.
  set (ind := merge xind yind).
  have?: sorted xind by admit. 
  have?: sorted yind by admit.
  have?: NoDup xind by admit. 
  have?: NoDup yind by admit.
  have ndind: NoDup ind by exact/sorted_nodup/sorted_merge.
  xin (1,0): (xwp;xapp=> ans); (xwp;xapp=> iX); 
    (xwp;xapp=> iY); (xwp;xapp=> step); (xwp;xapp=> stride)...
Admitted.


End alpha_blending.


End runlength.
