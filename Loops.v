Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct.
From SLF Require Import Fun LabType Sum.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Import List.

Open Scope Z_scope.

Module WithLoops (Dom : Domain).

Module Export AD := WithArray(Dom).

Arguments disjoint_inv_not_indom_both {_ _ _ _ _}.


(* Definition is_bool (v : val) := 
  if v is val_bool _ then true else false. *)

Lemma wp_Q_eq Q2 fs H Q1 : (forall hv, Q1 hv = Q2 hv) -> wp fs H Q1 = wp fs H Q2.
Proof. move=> ?; f_equal; exact/fun_ext_1. Qed.

Lemma wp_while_aux_false `{INH: Inhab D} i fs ht (H : int -> (D -> val) -> hhprop) Z N fsi hv0 :
  (forall j hv, Z <= j < N ->
    H j hv ==> 
      wp
        (fsi j) 
        ht 
        (fun hr => H (j+1) (hv \u_(Union (interval Z j) fsi) hr))) ->
  (Z <= i <= N) ->
  (forall j hv1 hv2, (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> H j hv1 = H j hv2) ->
  (forall i j, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi i) (fsi j)) ->
  fs = Union (interval i N) fsi ->
  H i hv0 ==> 
    wp
      fs
      ht 
      (fun hr => H N (hv0 \u_(Union (interval Z i) fsi) hr)).
Proof with autos*.
  move=> Step + hP Dj ->.
  move: hv0.
  induction_wf IH: (upto N) i; rewrite /upto le_zarith lt_zarith in IH.
  move=> hv0 ?.
  case: (classicT (i = N))=> [->|?].
  { rewrite intervalgt ?Union0 ?wp0_dep; last lia; xsimpl hv0.
    move=> ?; apply:applys_eq_init; fequal; extens=> ?.
    rewrite /uni; by case: classicT. }  
  rewrite intervalU ?Union_upd; last lia; first last.
  { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
    case=> [?[?|]|]; first by subst.
    { subst=> ?; apply/Dj=> //; lia. }
    move=> ? [?|?]; subst; apply/Dj; lia. }
  rewrite -wp_union; first last.
  { rewrite disjoint_Union=> ? /[! indom_interval]?; apply/Dj; lia. }
  apply/xapp_lemma; [rewrite -wp_equiv;apply/(Step _ hv0); lia|].
  xsimpl; unfold protect=> hv.
  apply/xapp_lemma; unfold protect.
  { rewrite -wp_equiv. apply/(IH _ _ ((hv0 \u_ (\U_(i <- `[Z, i]) fsi i)) hv)); lia. }
  xsimpl=> ?. erewrite hP; first exact: himpl_refl.
  move=> ? IN. rewrite {1 3}/uni intervalUr ?Union_upd ?indom_union_eq; last lia.
  { case: classicT=> [[]|].
    { case: classicT.
      { by rewrite /uni; case: classicT. }
      by rewrite /uni; do ? case: classicT. }
    { do ? (rewrite /uni; case: classicT=> //). }
    rewrite /uni. do ? case: classicT... }
  introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
  case=> [?[?|]|]; first by subst.
  { subst=> ?; apply/Dj=> //; lia. }
  move=> ? [?|?]; subst; apply/Dj; lia.
Qed.

Lemma wp_while_aux T `{INH: Inhab D} i fs fs' ht (H : bool -> int -> (D -> val) -> hhprop) Z N C fsi s hv0 b0 :
  (Z <= i <= N) ->
  (forall j b hv1 hv2, (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> H b j hv1 = H b j hv2) ->
  (forall i j, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi i) (fsi j)) ->
  fs = Union (interval i N) fsi ->
  fs' = `{s} ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (forall j, (i <= j < N) -> ~ indom (fsi j) s) ->
  (ht s = While C T) ->
  (forall hv i b, 
    Z <= i <= N ->
    htriple fs' (fun=> C) (H b i hv) (fun vb => \[vb s = b] \* H b i hv)) ->
  (forall hv b, H b N hv ==> \[b = false] \* H b N hv) ->
  (forall j hv, Z <= j < N ->
    H true j hv ==> 
      wp
        (fs' \u (fsi j)) 
        (upd ht s T) 
        (fun hr => \exists b', H b' (j+1) (hv \u_(Union (interval Z j) fsi) hr))) ->
  (forall j hv, Z <= j < N ->
    H false j hv ==> 
      wp
        (fsi j) 
        ht 
        (fun hr => H false (j+1) (hv \u_(Union (interval Z j) fsi) hr))) ->
  H b0 i hv0 ==> 
    wp
      (fs' \u fs)
      ht 
      (fun hr => H false N (hv0 \u_(Union (interval Z i) fsi) hr)).
Proof with autos*.
  move=> + hP Dj ->-> swhile scond stt cw cc ct ++ HNC HF.
  move: ht hv0 b0.
  induction_wf IH: (upto N) i; rewrite /upto le_zarith lt_zarith in IH.
  move=> ht hv0 b lN dj htE StepT StepF.
  have ?: disjoint (`{s}) (\U_(i <- `[i, N]) fsi i).
  { rewrite disjoint_Union=> ? /[! indom_interval]/dj?.
    rewrite disjoint_comm; applys* disjoint_single_of_not_indom. }
  rewrite -wp_union // wp_single htE /While /While_aux.
  rewrite wp_fix_app2.
  Opaque subst.
  xwp.
  Transparent subst.
  rewrite /= ?swhile stt cw ct; move/HNC: (lN)=> {}HNC.
  xapp=> cond; rewrite wp_single scond=>->.
  case: (classicT (i = N))=> [|?].
  { move=>->; eapply himpl_trans; eauto; xsimpl=>->.
    xwp; xif=> // _; xwp; xval.
    rewrite intervalgt ?Union0 ?wp0_dep; last lia; xsimpl hv0.
    by erewrite hP; autos*=> ??; rewrite uni_in. }
  xwp; xif; case: b=> // _.
  { rewrite intervalU ?Union_upd; last lia; first last.
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; lia. }
      move=> ? [?|?]; subst; apply/Dj; lia. }
    have ?: forall t (d : D), indom (fsi i) d -> upd ht s t d = ht d.
    { move=> ???; rewrite upd_neq // => ?; subst.
      apply/dj; eauto; lia. }
    set (t := <{_ ; _}>).
    rewrite wp_equiv; apply/htriple_conseq; [|eauto|]; first last.
    { move=> ?; rewrite -wp_union.
      { rewrite (wp_ht_eq _ (upd ht s t)); last symmetry...
        rewrite wp_equiv. apply/htriple_conseq; [|exact: himpl_refl|]; first last.
        { move=> v.
          rewrite wp_equiv; apply/htriple_conseq; [|exact: himpl_refl|]; first last.
          { move=> v'. rewrite (uniA _ _ _ v); exact: himpl_refl. }
          rewrite -wp_equiv; exact: himpl_refl. }
        rewrite -wp_equiv; exact: himpl_refl. }
      rewrite disjoint_Union=> ? /[!indom_interval]?; apply/Dj; lia. }
    rewrite -wp_equiv.
    rewrite (wp_ht_eq _ (upd ht s t)); first last.
    { move=> ?; rewrite indom_single_eq=>->; by rewrite upd_eq. }
    set (f := uni _ hv0). 
    set (Wp := wp (Union _ _) _).
    set (h := H false N).
    set (st := _ \u _).
    rewrite (wp_union (fun v => Wp (fun v' => h (f (uni st v v'))))); first last.
    { apply/disjoint_single_of_not_indom/dj; lia. }
    rewrite {}/f{}/Wp{}/h{}/st.
    rewrite wp_equiv. apply/(htriple_sequ2 _ _ (fun=> T) ht (htpre := upd ht s T)).
    { apply/disjoint_single_of_not_indom/dj; lia. }
    { move=> ?. rewrite indom_single_eq=>-> /[! upd_eq] //. }
    { eauto. }
    { rewrite -wp_equiv; apply/StepT; lia. }
    { move=> ?. rewrite indom_single_eq=>-> /[! upd_eq]; reflexivity. }
    { eauto. }
    move=> hv1. rewrite -wp_equiv -wp_fix_app2; xsimpl=> ?.
    rewrite -/(While_aux _ _) -/(While _ _).
    { rewrite (wp_ht_eq _ ht); first last.
      { move=> ?; rewrite indom_single_eq=><-... }
      under wp_Q_eq.
      { move=> hv'. set (f := uni _ hv0).
        rewrite (wp_Q_eq (fun hv => H false N (f hv1 \u_(\U_(i <- `[Z, i+1]) fsi i) (hv' \u_(`{s}) hv)))).
        { over. }
        move=> ?. f_equal; rewrite /f; extens=> ?.
        rewrite /uni intervalUr; last lia. 
        rewrite Union_upd ?indom_union_eq.
        { do ? case: classicT... case=> //; rewrite indom_single_eq.
          move=> /[swap]<- /dj. case; lia. }
        introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
        case=> [?[?|]|]; first by subst.
        { subst=> ?; apply/Dj=> //; lia. }
        move=> ? [?|?]; subst; apply/Dj; lia. } 
      rewrite (wp_union (fun v => H _ _ (_ \u_ _ v))); first last.
      { rewrite disjoint_Union=> ?/[!indom_interval] ?.
        rewrite disjoint_comm; apply/disjoint_single_of_not_indom/dj; lia. }
      apply/IH; (try lia)...
      move=> ??; apply/dj; lia. } 
      move=> hv1 hv2 hvE; erewrite wp_Q_eq; first exact: himpl_refl.
      do 3 (f_equal=> > /=); extens=> ?. 
      rewrite /uni; case: classicT... }
  xwp; xval=> ?.
  pose proof wp_while_aux_false; move: H0 StepF=> /[apply]/[apply] HH.
  apply/wp_conseq; last apply/HH...
  move=> ?. erewrite hP; first exact: himpl_refl.
  move=> ?.
  rewrite /uni; do ? case: classicT...
  rewrite indom_single_eq=> <- IN /[!@indom_Union]-[]y.
  rewrite indom_interval=> -[]?/[dup]?/dj-[].
  apply:not_not_inv=> ?; apply/IN; rewrite indom_Union. 
  exists y; split=> //; rewrite indom_interval; lia.
Qed.

Lemma wp_while `{INH: Inhab D} fs fs' ht (H : bool -> int -> (D -> val) -> hhprop) Z N T C fsi s hv0 b0 P Q:
  (Z <= N) ->
  (forall j b hv1 hv2, (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> H b j hv1 = H b j hv2) ->
  (P ==> H b0 Z hv0) -> 
  (H false N ===> Q) ->
  (forall i j, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi i) (fsi j)) ->
  fs = Union (interval Z N) fsi ->
  fs' = `{s} ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (forall j, (Z <= j < N) -> ~ indom (fsi j) s) ->
  (ht s = While C T) ->
  (forall hv i b, 
      Z <= i <= N ->
      htriple fs' (fun=> C) (H b i hv) (fun vb => \[vb s = b] \* H b i hv)) ->
  (forall hv b, H b N hv ==> \[b = false] \* H b N hv) ->
  (forall j hv, Z <= j < N ->
    H true j hv ==> 
      wp
        (fs' \u (fsi j)) 
        (upd ht s T) 
        (fun hr => \exists b', H b' (j+1) (hv \u_(Union (interval Z j) fsi) hr))) ->
  (forall j hv, Z <= j < N ->
    H false j hv ==> 
      wp
        (fsi j) 
        ht 
        (fun hr => H false (j+1) (hv \u_(Union (interval Z j) fsi) hr))) ->
  P ==> wp (fs' \u fs) ht Q.
Proof with autos*.
  move=> ? hP *. apply: himpl_trans; eauto.
  apply: himpl_trans; [|apply:wp_conseq; eauto].
  apply: himpl_trans.
  { apply/(@wp_while_aux T); try eassumption; lia. }
  apply/wp_conseq=> ?; erewrite hP; first exact: himpl_refl.
  move=> ??; rewrite intervalgt ?Union0 ?uni0 //; lia.
Qed.

Lemma xwhile_big_op_lemma_aux `{INH: Inhab D} Inv (R R' : Dom.type -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1
  Z N (C1 : Dom.type -> trm) (i j : int) (C T : trm) b0
  Pre Post: 
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv true l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R d) \* 
       p ~⟨(i, 0%Z), s⟩~> (val_int x) }}
      [{
        {i| _  in `{s}  => T};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, \exists b,
        Inv b (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' d) \* 
        p ~⟨(i, 0%Z), s⟩~> (val_int (x + (op hv l))) }}) ->
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv false l \* 
       \*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R d}}
      [{
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, \[op hv l = 0] \*
        Inv false (l + 1) \* 
        \*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' d}}) ->
  (forall (l : int) (b : bool), 
    Z <= l <= N ->
    {{ Inv b l }}
      [{
        {i| _  in `{s}  => C}
      }]
    {{ hv, \[hv[`i](s) = b] \* Inv b l }}) ->
  (forall b, Inv b N ==> \[b = false] \* Inv b N) ->
  (forall i j : int, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi1 i) (fsi1 j)) ->
  (forall (hv hv' : D -> val) m,
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    op hv m = op hv' m) ->
  (i <> j) ->
  (Z <= N)%Z ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (Pre ==> 
    Inv b0 Z \* 
    (\*_(d <- Union (interval Z N) fsi1) R d) \*
    p ~⟨(i, 0%Z), s⟩~> val_int 0) ->
  (forall hv, 
    Inv false N \* 
    (\*_(d <- Union (interval Z N) fsi1) R' d) \* 
    p ~⟨(i, 0%Z), s⟩~> val_int (Σ_(i <- interval Z N) (op hv i)) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => While C T};
      {j| ld in Union (interval Z N) fsi1 => C1 ld}
    }]
  {{ hv, Post hv }}.
Proof.
  move=> IHT IHF IHC IHN Dj opP iNj ?? ??? ??? PostH.
  apply:himpl_trans; first eauto.
  rewrite /ntriple /nwp ?fset_of_cons /=.
  apply: himpl_trans; first last.
  { apply/wp_conseq=> ?; apply PostH. }
  rewrite ?Union_label union_empty_r.
  eapply wp_while with 
    (C := C)
    (H:=(fun b q hv => 
      Inv b q \* 
      (\*_(d <- Union (interval Z q) fsi1) R' d) \*
      (\*_(d <- Union (interval q N) fsi1) R d) \* 
      p ~⟨(i, 0%Z), s⟩~> Σ_(l <- interval Z q) op hv l))
    (hv0:=fun=> 0)=> //; try eassumption.
  { move=> r b hv hv' hvE.
    suff->:
      Σ_(l <- interval Z r) op hv l = 
      Σ_(l <- interval Z r) op hv' l by xsimpl.
    apply/SumEq=> *; apply/opP=> *; apply/hvE.
    rewrite indom_Union; eexists; rewrite indom_label_eq; autos*. }
  { rewrite [_ Z Z]intervalgt; last math.
    rewrite Union0 hbig_fset_empty Sum0. xsimpl. }
  { move=> ?.
    rewrite [_ N N]intervalgt; last math.
    rewrite Union0 hbig_fset_empty. xsimpl. }
  { simpl.
    intros. apply disjoint_of_not_indom_both. 
    intros. destruct x as (?, x). 
    rewrite indom_label_eq in H2. rewrite indom_label_eq in H3.
    destruct H2 as (_ & H2), H3 as (_ & H3). 
    revert H2 H3. apply disjoint_inv_not_indom_both, Dj=> //; math. }
  { rewrite label_single; reflexivity. }
  { move=> ?? /=; rewrite indom_label_eq=> -[][]. eqsolve. }
  { rewrite /htrm_of /=; case: classicT=> //=> []; split*. }
  { clear -IHC Dj iNj opP.
    move=> hv l b /IHC-/(_ b).
    rewrite /ntriple/nwp ?fset_of_cons /= ?fset_of_nil union_empty_r.
    rewrite /htrm_of label_single wp_single /= indom_single_eq.
    do ? case: classicT; autos*=> _.
    rewrite -wp_equiv wp_equiv=> HT; xapp; xsimpl*. }
  { move=> ??. xchange IHN; xsimpl*. }
  { clear -IHT Dj iNj opP.
    move=> l hv /[dup]?/IHT. 
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
    rewrite union_empty_r intervalUr; last lia.
    rewrite Union_upd //; first last. 
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; math. }
      move=> ? [?|?]; subst; apply/Dj; math. }
    rewrite hbig_fset_union; first last; eauto; try by (hnf; auto).
    { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj; math. }
    rewrite (@intervalU l N); last math.
    rewrite Union_upd //; first last.
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; math. }
      move=> ? [?|?]; subst; apply/Dj; math. }
    rewrite hbig_fset_union; first last; eauto; try by (hnf; auto).
    { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj; math. }
    setoid_rewrite wp_equiv at 1=> Hwp.
    erewrite wp_ht_eq with (ht2:=(htrm_of
      ((Lab (pair i 0) (FH (single s tt) (fun=> T))) ::
        (Lab (pair j 0) (FH (fsi1 l) (fun ld => C1 ld))) ::
        nil))).
    2:{ intros (ll, d) H. unfold upd, htrm_of. simpl. 
      rewrite indom_union_eq ! indom_label_eq in H |- *.
      rewrite indom_single_eq in H |- *.
      repeat case_if; try eqsolve.
      destruct C4 as (<- & HH). false C3. split; auto.
      rewrite indom_Union. exists l. rewrite indom_interval.
      split; try math; auto. }
    xapp=> {}hr ?; xsimpl.
    rewrite <- intervalUr; try math. rewrite SumxSx; try math.
    move=> ?; apply:applys_eq_init. 
    do 3 f_equal; [apply/SumEq=> ??|]; apply/opP=> ? IN*; 
    rewrite /uni indom_Union; case: classicT=> //.
    { case; eexists; splits*; rewrite indom_label_eq; autos*. }
    case=> l' []/[!@indom_label_eq]/[!indom_interval]=> ?.
    case=> _ /disjoint_inv_not_indom_both /(_ IN)-[].
    apply/Dj; lia. }
  clear -IHF Dj iNj opP.
  move=> l hv /[dup]?/IHF. 
  rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
  rewrite union_empty_r intervalUr; last lia.
  rewrite Union_upd //; first last. 
  { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
    case=> [?[?|]|]; first by subst.
    { subst=> ?; apply/Dj=> //; math. }
    move=> ? [?|?]; subst; apply/Dj; math. }
  rewrite hbig_fset_union; first last; eauto; try by (hnf; auto).
  { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj; math. }
  rewrite (@intervalU l N); last math.
  rewrite Union_upd //; first last.
  { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
    case=> [?[?|]|]; first by subst.
    { subst=> ?; apply/Dj=> //; math. }
    move=> ? [?|?]; subst; apply/Dj; math. }
  rewrite hbig_fset_union; first last; eauto; try by (hnf; auto).
  { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj; math. }
  setoid_rewrite wp_equiv at 1=> Hwp.
  erewrite wp_ht_eq with (ht2:=(htrm_of
    ((Lab (pair j 0) (FH (fsi1 l) (fun ld => C1 ld))) ::
      nil))).
  2:{ intros (ll, d) H. unfold uni, htrm_of. simpl. 
    rewrite ! indom_label_eq in H |- *.
    rewrite indom_single_eq in H |- *. 
    repeat case_if; try eqsolve.
    destruct C3 as (<- & HH). false C2. split; auto.
    rewrite indom_Union. exists l. rewrite indom_interval.
    split; try math; auto. }
  xapp=> {}hr; xsimpl.
  move=> E0 ?; apply:applys_eq_init. 
  rewrite <- intervalUr; try math. rewrite SumxSx; try math.
  Search (_ + 0).
  do 2 f_equal; rewrite (opP _ hr) ?E0
  [apply/SumEq=> ??|]; apply/opP=> ? IN*; 
  rewrite /uni indom_Union; case: classicT=> //.
  { case; eexists; splits*; rewrite indom_label_eq; autos*. }
  case=> l' []/[!@indom_label_eq]/[!indom_interval]=> ?.
  case=> _ /disjoint_inv_not_indom_both /(_ IN)-[].
  apply/Dj; lia.
Qed.

Lemma wp_while_unary `{Inhab D} fs' (Inv : bool -> int -> hhprop) Z N T C s b0 (P : hhprop) Q :
  (forall (b : bool) (x : int),
    Inv b x ==>
      wp 
        fs'
        (fun=> C) 
        (fun hc => \[hc s = b] \* Inv b x)) -> 
  (forall x, Inv false x ==> \[(x = N)] \* Inv false x) ->
  (forall x, Inv true x ==> \[(x < N)] \* Inv true x) ->
  (forall j, (Z <= j < N) ->
    (forall j' b', 
      htriple fs'
        (fun=> While C T) 
        (Inv b' j' \* \[j < j' <= N])
        (fun=> Inv false N)) ->
    Inv true j ==> 
        wp
          fs' 
          (fun=> trm_seq T (While C T))
          (fun=> Inv false N)) ->
  P ==> Inv b0 Z ->
  (fun=> Inv false N) ===> Q ->
  (Z <= N) ->
  fs' = single s tt  ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  P ==> wp fs' (fun=> While C T) Q.
Proof.
  move=> HwpC HwpF HwpT HwpT' HP HQ *.
  apply: himpl_trans; first exact/HP.
  apply: himpl_trans; first last.
  { apply: wp_conseq; exact/HQ. }
  apply: himpl_trans.
  { apply/(wp_while_aux_unary (Z := Z) (i := Z) _ (T := T)); eauto. math. }
  by [].
Qed.

Ltac xwhile1 Z N b Inv := 
  let N := constr:(N) in
  let Z := constr:(Z) in 
  let Inv' := constr:(Inv) in
  xseq_xlet_if_needed; xstruct_if_needed;
  eapply (wp_while_unary Inv b (Z := Z) (N := N)); autos*.


Lemma xfor_big_op_lemma_aux `{INH: Inhab D} Inv (R R' : Dom.type -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1 vr
  Z N (C1 : Dom.type -> trm) (i j : int) (C : trm)
  Pre Post: 
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R d) \* 
       p ~⟨(i, 0%Z), s⟩~> (val_int x) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' d) \* 
        p ~⟨(i, 0%Z), s⟩~> (val_int (x + (op hv l))) }}) ->
  (forall i0 j0 : int, i0 <> j0 -> Z <= i0 < N -> Z <= j0 < N -> disjoint (fsi1 i0) (fsi1 j0)) ->
  (forall (hv hv' : D -> val) m,
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    op hv m = op hv' m) ->
  (i <> j) ->
  (Z <= N)%Z ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi1) R d) \*
    p ~⟨(i, 0%Z), s⟩~> val_int 0) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi1) R' d) \* 
    p ~⟨(i, 0%Z), s⟩~> val_int (Σ_(i <- interval Z N) (op hv i)) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For Z N (trm_fun vr C)};
      {j| ld in Union (interval Z N) fsi1 => C1 ld}
    }]
  {{ hv, Post hv }}.
Proof.
  move=> IH Dj opP iNj ?? ??? ??? PostH.
  apply:himpl_trans; first eauto.
  rewrite /ntriple /nwp ?fset_of_cons /=.
  apply: himpl_trans; first last.
  { apply/wp_conseq=> ?; apply PostH. }
  rewrite ?Union_label union_empty_r.
  eapply wp_for with 
    (H:=(fun q hv => 
      Inv q \* 
      (\*_(d <- Union (interval Z q) fsi1) R' d) \*
      (\*_(d <- Union (interval q N) fsi1) R d) \* 
      p ~⟨(i, 0%Z), s⟩~> Σ_(l <- interval Z q) op hv l))
    (hv0:=fun=> 0)=> //; try eassumption.
  { clear -IH Dj iNj opP.
    move=>l hv ?; move: (IH l).
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
    rewrite union_empty_r intervalUr; try math.
    rewrite Union_upd //; first last. 
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; math. }
      move=> ? [?|?]; subst; apply/Dj; math. }
    rewrite hbig_fset_union; first last.
    2-4: auto.
    2-3: hnf; auto.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    rewrite (@intervalU l N); last math.
    rewrite Union_upd //; first last.
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; math. }
      move=> ? [?|?]; subst; apply/Dj; math. }
    rewrite // hbig_fset_union; first last.
    2-4: auto.
    2-3: hnf; auto.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    move=> Hwp.
    erewrite wp_ht_eq with (ht2:=(htrm_of
      ((Lab (pair i 0) (FH (single s tt) (fun=> subst vr l C))) ::
        (Lab (pair j 0) (FH (fsi1 l) (fun ld => C1 ld))) ::
        nil))).
    2:{
      intros (ll, d) H. unfold uni, htrm_of. simpl. 
      rewrite indom_union_eq ! indom_label_eq in H |- *.
      rewrite indom_single_eq in H |- *. 
      repeat case_if; try eqsolve.
      destruct C3 as (<- & HH). false C2. split; auto.
      rewrite indom_Union. exists l. rewrite indom_interval.
      split; try math; auto.
    }
    assert (Z <= l < N) as Htmp by math. 
    specialize (Hwp (Sum (interval Z l) (fun i => op hv i)) Htmp). clear Htmp.
    apply wp_equiv in Hwp. apply wp_equiv.
    eapply htriple_conseq_frame.
    1: apply Hwp.
    1: xsimpl. 1: xsimpl.
    hnf. intros v.
    xsimpl. xsimpl.
    rewrite <- intervalUr; try math. rewrite SumxSx; try math.
    hnf. intros h Hh. apply hsingle_inv in Hh. subst h.
    rewrite -> SumEq with (G:=fun i => op hv i).
    2:{ intros x. rewrite indom_interval. 
      unfold uni. intros HH. apply opP.
      intros. rewrite indom_label_eq. case_if; auto.
      destruct C0 as (_ & H0).
      false disjoint_inv_not_indom_both. 2: apply H. 2: apply H0.
      apply Dj; math.
    }
    rewrite -> opP with (hv':=v). 1: apply hsingle_intro.
    intros. unfold uni. rewrite indom_label_eq. case_if; eqsolve. }
  { move=> r hv hv' hvE.
    suff->:
      Σ_(l <- interval Z r) op hv l = 
      Σ_(l <- interval Z r) op hv' l by xsimpl.
    apply/SumEq=> *; apply/opP=> *; apply/hvE.
    rewrite indom_Union; eexists; rewrite indom_label_eq; autos*. }
  { rewrite [_ Z Z]intervalgt; last math.
    rewrite Union0 hbig_fset_empty Sum0. xsimpl. }
  { move=> ?.
    rewrite [_ N N]intervalgt; last math.
    rewrite Union0 hbig_fset_empty. xsimpl. }
  { simpl.
    intros. apply disjoint_of_not_indom_both. 
    intros. destruct x as (?, x). 
    rewrite indom_label_eq in H2. rewrite indom_label_eq in H3.
    destruct H2 as (_ & H2), H3 as (_ & H3). 
    revert H2 H3. apply disjoint_inv_not_indom_both, Dj=> //; math.
  }
  { rewrite disjoint_Union=> ??. 
    apply disjoint_of_not_indom_both. 
    intros. destruct x as (?, x).
    simpl in H. rewrite indom_single_eq in H.  
    injection H as <-.
    rewrite -> indom_Union in H0.
    destruct H0 as (? & ? & H0).
    rewrite indom_label_eq in H0. eqsolve.
  }
  by case=> l d; rewrite indom_label_eq /= /htrm_of; case: classicT.
Qed.

Lemma xfor_specialized_lemma `{INH: Inhab D} (Inv : int -> hhprop) (R R' : Dom.type -> hhprop) 
  s fsi1 vr
  Z N (C1 : Dom.type -> trm) (i j : int) (C : trm)
  Pre Post
  (p : Dom.type -> loc) : 
  (forall (l : int),
    Z <= l < N ->
    {{ Inv l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R d) \*
       (\*_(d <- (fsi1 l)) p d ~⟨(i, 0%Z), s⟩~> val_uninit) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' d) \*
        (\*_(d <- (fsi1 l)) p d ~⟨(i, 0%Z), s⟩~> hv (Lab (j, 0%Z) d)) }}) ->
  (forall i0 j0 : int, i0 <> j0 -> disjoint (fsi1 i0) (fsi1 j0)) ->
  (i <> j) ->
  (Z <= N)%Z ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi1) R d) \*
    (\*_(d <- Union (interval Z N) fsi1) p d ~⟨(i, 0%Z), s⟩~> val_uninit)) ->
  (forall hv,
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi1) R' d) \*
    (\*_(d <- Union (interval Z N) fsi1) p d ~⟨(i, 0%Z), s⟩~> hv (Lab (j, 0%Z) d)) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For Z N (trm_fun vr C)};
      {j| ld in Union (interval Z N) fsi1 => C1 ld}
    }]
  {{ hv, Post hv }}.
Proof.
  move=> IH Dj iNj ?? ??? ??? PostH.
  apply:himpl_trans; first eauto.
  rewrite /ntriple /nwp ?fset_of_cons /=.
  apply: himpl_trans; first last.
  { apply/wp_conseq=> ?; apply PostH. }
  rewrite ?Union_label union_empty_r.
  eapply wp_for with 
    (H:=(fun q hv => 
      Inv q \* 
      (\*_(d <- Union (interval Z q) fsi1) R' d) \*
      (\*_(d <- Union (interval q N) fsi1) R d) \* 
      (\*_(d <- Union (interval Z q) fsi1) p d ~⟨(i, 0%Z), s⟩~> hv (Lab (j, 0%Z) d)) \*
      (\*_(d <- Union (interval q N) fsi1) p d ~⟨(i, 0%Z), s⟩~> val_uninit)))
    (hv0:=fun=> 0) => //; try eassumption.
  { clear -IH Dj iNj.
    move=>l hv ?. 
    move: (IH l).
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
    rewrite union_empty_r intervalUr; try math.
    rewrite Union_upd //; first last.
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; math. }
      move=> ? [?|?]; subst; apply/Dj; math. }
    rewrite hbig_fset_union; first last.
    2-4: auto.
    2-3: hnf; auto.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    rewrite (@intervalU l N); last math.
    rewrite Union_upd; first last. 
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; math. }
      move=> ? [?|?]; subst; apply/Dj; math. }
    rewrite hbig_fset_union; first last.
    2-4: auto.
    2-3: hnf; auto.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    move=> Hwp.
    rewrite -> hbig_fset_union.
    2-3: hnf; auto.
    2: auto.
    2: { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    erewrite wp_ht_eq with (ht2:=(htrm_of
      ((Lab (pair i 0) (FH (single s tt) (fun=> subst vr l C))) ::
        (Lab (pair j 0) (FH (fsi1 l) (fun ld => C1 ld))) ::
        nil))).
    2:{
      intros (ll, d) H. unfold uni, htrm_of. simpl. 
      rewrite indom_union_eq ! indom_label_eq in H |- *.
      rewrite indom_single_eq in H |- *. 
      repeat case_if; try eqsolve.
      destruct C3 as (<- & HH). false C2. split; auto.
      rewrite indom_Union. exists l. rewrite indom_interval.
      split; try math; auto.
    }
    assert (Z <= l < N) as Htmp by math. specialize (Hwp Htmp). clear Htmp.
    apply wp_equiv in Hwp. apply wp_equiv.
    eapply htriple_conseq_frame.
    1: apply Hwp.
    1: xsimpl. 1: xsimpl.
    hnf. intros v.
    xsimpl. xsimpl.
    rewrite -> hbig_fset_union.
    2-3: hnf; auto.
    2: auto.
    2: { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; math. }
    unfold uni.
    apply himpl_frame_lr.
    { apply hbig_fset_himpl.
      intros. case_if; auto.
      rewrite indom_label_eq in C0. eqsolve.
    }
    { apply hbig_fset_himpl.
      intros. case_if; auto.
      rewrite indom_label_eq in C0. destruct C0 as (_ & H1).
      rewrite indom_Union in H. 
      destruct H as (f & H & H2). rewrite -> indom_interval in H.
      false. revert H1 H2. apply disjoint_inv_not_indom_both, Dj.
      math.
    }
  }
  { intros. f_equal. f_equal. f_equal. f_equal. apply hbig_fset_eq.
    intros. rewrite -> H; auto.
    rewrite indom_Union in H0. rewrite indom_Union.
    destruct H0 as (f & H0 & H2). 
    exists f. rewrite indom_label_eq. intuition.
  }
  { rewrite [_ Z Z]intervalgt; last math.
    rewrite Union0 ! hbig_fset_empty. xsimpl. }
  { move=> ?.
    rewrite [_ N N]intervalgt; last math.
    rewrite Union0 ! hbig_fset_empty. xsimpl. }
  { simpl.
    intros. apply disjoint_of_not_indom_both. 
    intros. destruct x as (?, x).
    rewrite indom_label_eq in H2. rewrite indom_label_eq in H3.
    destruct H2 as (_ & H2), H3 as (_ & H3). 
    revert H2 H3. by apply disjoint_inv_not_indom_both, Dj.
  }
  { rewrite disjoint_Union=> ??. 
    apply disjoint_of_not_indom_both. 
    intros. destruct x as (?, x).
    simpl in H. rewrite indom_single_eq in H.  
    injection H as <-.
    rewrite -> indom_Union in H0.
    destruct H0 as (? & ? & H0).
    rewrite indom_label_eq in H0. eqsolve.
  }
  by case=> l d; rewrite indom_label_eq /= /htrm_of; case: classicT.
Qed.

Lemma lab_eqbE l1 l2: 
  (lab_eqb l1 l2) = (l1 = l2) :> Prop.
Proof. by extens; split=> [/lab_eqbP|->]// /[! eqbxx]. Qed.

Lemma xfor_big_op_lemma `{Inhab D} Inv (R R' : Dom.type -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1 vr
  Z N (C1 : Dom.type -> trm) (i j : int) (C : trm) C'
  Pre Post: 
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R d) \* 
       p ~⟨(i, 0%Z), s⟩~> (val_int x) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' d) \* 
        p ~⟨(i, 0%Z), s⟩~> (val_int (x + (op hv l))) }}) ->
  (forall i j : int, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi1 i) (fsi1 j)) ->
  (forall (hv hv' : D -> val) m,
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    op hv m = op hv' m) ->
  (i <> j) ->
  (Z <= N)%Z ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi1) R d) \*
    p ~⟨(i, 0%Z), s⟩~> val_int 0) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi1) R' d) \* 
    p ~⟨(i, 0%Z), s⟩~> val_int (Σ_(i <- interval Z N) (op hv i)) ==>
    wp ⟨(i,0),single s tt⟩ (fun=> C') (fun hr' => Post (lab_fun_upd hr' hv (i,0)))) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => trm_seq (For Z N (trm_fun vr C)) C'};
      {j| ld in Union (interval Z N) fsi1 => C1 ld}
    }]
  {{ hv, Post hv }}.
Proof.
  intros.
  xfocus (j,0); rewrite ?eqbxx.
  have E: (lab_eqb (i, 0) (j,0) = false).
  { by apply/bool_ext; split=> //; rewrite lab_eqbE=> -[]. }
  rewrite E/= -xnwp1_lemma /= wp_equiv.
  apply/htriple_conseq; [|eauto|]; first last.
  { move=> ?. apply/wp_seq. }
  rewrite (xnwp1_lemma (FH (single s tt) (fun=> For Z N <{ fun_ {vr} => {C} }>)) ((i,0))).
  rewrite -wp_equiv.
  apply/(xunfocus_lemma (fun hr => WP [ _ in ⟨(i, 0), single s tt⟩  => C' ]
  { hr'0, Post ((hr \u_ ⟨(j, 0), Union (interval Z N) fsi1⟩) hr'0) }))=> /=; autos*.
  { by rewrite E. }
  move=> ??; fequals; apply/fun_ext_1=> ?. fequals.
  extens=> -[]??; rewrite /uni; case: classicT=> //.
  xfocus (i,0); rewrite ?eqbxx lab_eqb_sym E /=.
  apply/xunfocus_lemma; autos*=> /=.
  { by rewrite lab_eqb_sym E. }
  { move=> ??. remember ((_ \u_ _) _); reflexivity. }
  simpl.
  apply/xfor_big_op_lemma_aux; eauto.
  move=> hv. apply: himpl_trans; [|apply/wp_hv].
  move: (H12 hv); rewrite wp_equiv=> ?.
  xapp=> hv'. rewrite -/(lab_fun_upd _ _ _).
  xsimpl (lab_fun_upd hv' hv (i, 0))=> ?.
  apply: applys_eq_init; fequals; apply/fun_ext_1=> /=.
  case=> l x.
  rewrite /uni ?indom_label_eq; case: classicT.
  { by case=> <- /=; rewrite lab_eqb_sym E. }
  case: classicT=> //.
  case=> <- /=; rewrite eqbxx //.
Qed.

Tactic Notation "xfor_sum" constr(Inv) constr(R) uconstr(R') uconstr(op) constr(s) :=
  eapply (@xfor_big_op_lemma _ Inv R R' op s); 
  [ let L := fresh in 
    intros ?? L;
    xnsimpl
  | let Neq := fresh in
    let i   := fresh "i" in
    let j   := fresh "j" in 
    intros i j; 
    autorewrite with disjointE; try math
  | let hvE := fresh "hvE" in
    let someindom := fresh "someindom" in
    intros ??? hvE; rewrite ?/op;
    match goal with 
    | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ? someindom; extens; intros 
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
  ]=> //; autos*.

Lemma disjoint_single {T} (x y : T) : 
  disjoint (single x tt) (single y tt) = (x <> y).
Proof.
  extens; split; last apply/disjoint_single_single.
  move/[swap]->; exact/disjoint_single_single_same_inv.
Qed.

Lemma disjoint_interval (x1 y1 x2 y2 : int) : 
  disjoint (interval x1 y1) (interval x2 y2) = ((y1 <= x2) \/ (y2 <= x1) \/ (y1 <= x1) \/ (y2 <= x2)).
Proof.
  extens; split=> [/(@disjoint_inv_not_indom_both _ _ _ _ _)|].
  { setoid_rewrite indom_interval=> /[dup]/(_ x1)+/(_ x2).
   lia. }
  move=> H; apply/disjoint_of_not_indom_both=> ?; rewrite ?indom_interval.
  move: H; lia.
Qed.

Lemma disjoint_single_interval (x1 y1 x : int) : 
  disjoint (single x tt) (interval x1 y1) = ((x < x1) \/ (y1 <= x)).
Proof.
  extens; split=> [/(@disjoint_inv_not_indom_both _ _ _ _ _)|].
  { move=> /[dup]/(_ x); rewrite indom_interval indom_single_eq.
    lia. }
  move=> H; apply/disjoint_single_of_not_indom.
  rewrite indom_interval. math.
Qed.


Lemma disjoint_interval_single (x1 y1 x : int) : 
  disjoint (interval x1 y1) (single x tt) = ((x < x1) \/ (y1 <= x)).
Proof. by rewrite disjoint_comm disjoint_single_interval. Qed.

Lemma disjoint_label {T} (l l' : labType) (fs1 fs2 : fset T) : 
  disjoint (label (Lab l fs1)) (label (Lab l' fs2)) = ((l <> l') \/ disjoint fs1 fs2).
Proof.
  extens; split=> [/(@disjoint_inv_not_indom_both _ _ _ _ _)|].
  { move=> IN; case: (classicT (l = l')); [right|left]=> //; subst.
    apply/disjoint_of_not_indom_both=> x.
    move: (IN (Lab l' x)); rewrite ?indom_label_eq; autos*. }
  case: (classicT (l = l'))=> [<-|? _].
  { rewrite*  @disjoint_eq_label. }
  apply/disjoint_of_not_indom_both=> -[??]; rewrite ?indom_label_eq.
  case=><-; autos*.
Qed.


Global Hint Rewrite @disjoint_single disjoint_interval disjoint_single_interval 
  disjoint_interval_single @disjoint_eq_label @disjoint_label : disjointE.

End WithLoops.