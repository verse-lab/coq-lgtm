Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibListExt LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl LibArray.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Import List.

Open Scope Z_scope.

Section WithLoops.

(* Context {D : Type}. *)

Lemma wp_Q_eq {D : Type} Q2 fs H (Q1 : _ -> hhprop D) : (forall hv, Q1 hv = Q2 hv) -> wp fs H Q1 = wp fs H Q2.
Proof. move=> ?; f_equal; exact/fun_ext_1. Qed.

Lemma wp_while_aux_false {D : Type} `{INH: Inhab D} i fs ht (H : int -> (D -> val) -> hhprop D) Z N fsi hv0 :
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

Lemma wp_while_aux {D : Type} T `{INH: Inhab D} i fs fs' ht (H : bool -> int -> (D -> val) -> hhprop D) Z N C fsi s hv0 b0 :
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
    rewrite (wp_ht_eq _ ht); first last.
    { move=> ?; rewrite indom_single_eq=><-... }
    under wp_Q_eq.
    { move=> hv'. set (f := uni _ hv0).
      rewrite (wp_Q_eq (fun hv => H false N (f hv1 \u_(\U_(i <- `[Z, i+1]) fsi i) (hv' \u_(`{s}) hv)))).
      { over. }
      move=> ?. f_equal; rewrite /f; extens=> ?.
      rewrite /uni intervalUr; last lia. 
      rewrite Union_upd ?indom_union_eq.
      { do ? case: classicT... }
      introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; lia. }
      move=> ? [?|?]; subst; apply/Dj; lia. } 
    rewrite (wp_union (fun v => H _ _ (_ \u_ _ v))); first last.
    { rewrite disjoint_Union=> ?/[!indom_interval] ?.
      rewrite disjoint_comm; apply/disjoint_single_of_not_indom/dj; lia. }
    apply/IH; (try lia)...
    move=> ??; apply/dj; lia. } 
  xwp; xval=> ?.
  pose proof @wp_while_aux_false; move: H0 StepF=> /[apply]/[apply] HH.
  apply/wp_conseq; last apply/HH...
  move=> ?. erewrite hP; first exact: himpl_refl.
  move=> ?.
  rewrite /uni; do ? case: classicT...
  rewrite indom_single_eq=> <- IN /[!@indom_Union]-[]y.
  rewrite indom_interval=> -[]?/[dup]?/dj-[].
  apply:not_not_inv=> ?; apply/IN; rewrite indom_Union. 
  exists y; split=> //; rewrite indom_interval; lia.
Qed.

Lemma wp_while {D : Type} `{INH: Inhab D} fs fs' ht (H : bool -> int -> (D -> val) -> hhprop D) Z N T C fsi s hv0 b0 P Q:
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
  { apply/(@wp_while_aux D T); try eassumption; lia. }
  apply/wp_conseq=> ?; erewrite hP; first exact: himpl_refl.
  move=> ??; rewrite intervalgt ?Union0 ?uni0 //; lia.
Qed.

Lemma wp_while_unary {D : Type} `{Inhab D} fs' (Inv : bool -> int -> hhprop D) Z N T C s b0 (P : hhprop D) Q :
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

Context {Dom : Type}.

Local Notation D := (labeled Dom).
Local Notation hhprop := (hhprop D).

(* Definition eld : D -> Dom := el. *)

Definition eld := (@eld Dom).

Local Coercion eld : D >-> Dom.

Lemma xwhile_big_op_lemma_aux `{INH: Inhab D} Inv (R R' : Dom -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1
  Z N (C1 : Dom -> trm) (i j : int) (C T : trm) b0
  Pre Post: 
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv true l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R (el d)) \* 
       p ~⟨(i, 0%Z), s⟩~> (val_int x) }}
      [{
        {i| _  in `{s}  => T};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, \exists b,
        Inv b (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' (el d)) \* 
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
  do 2 f_equal; rewrite (opP _ hr) ?E0 ?Z.add_0_r; 
  [apply/SumEq=> ??; apply/opP|]=> ? IN*; rewrite /uni indom_Union; case: classicT=> //.
  { case; eexists; splits*; rewrite indom_label_eq; autos*. }
  case=> l' []/[!@indom_label_eq]/[!indom_interval]=> ?.
  case=> _ /disjoint_inv_not_indom_both /(_ IN)-[].
  apply/Dj; lia.
Qed.

Lemma xwhile_big_op_lemma_aux2 `{INH: Inhab D} Inv (R1 R2 R1' R2' : Dom -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1 fsi2
  Z N (C1 C2 : Dom -> trm) (i j k : int) (C T : trm) b0
  Pre Post: 
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv true l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R1 d) \* 
       (\*_(d <- ⟨(k, 0%Z), fsi2 l⟩) R2 d) \* 
       p ~⟨(i, 0%Z), s⟩~> (val_int x) }}
      [{
        {i| _  in `{s}  => T};
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ hv, \exists b,
        Inv b (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R1' d) \*
        (\*_(d <- ⟨(k, 0%Z), fsi2 l⟩) R2' d) \* 
        p ~⟨(i, 0%Z), s⟩~> (val_int (x + (op hv l))) }}) ->
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv false l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R1 d) \*
        \*_(d <- ⟨(k, 0%Z), fsi2 l⟩) R2 d }}
      [{
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ hv, \[op hv l = 0] \*
        Inv false (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R1' d) \* 
         \*_(d <- ⟨(k, 0%Z), fsi2 l⟩) R2' d}}) ->
  (forall (l : int) (b : bool), 
    Z <= l <= N ->
    {{ Inv b l }}
      [{
        {i| _  in `{s}  => C}
      }]
    {{ hv, \[hv[`i](s) = b] \* Inv b l }}) ->
  (forall b, Inv b N ==> \[b = false] \* Inv b N) ->
  (forall i j : int, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi1 i) (fsi1 j)) ->
  (forall i j : int, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi2 i) (fsi2 j)) ->
  (forall (hv hv' : D -> val) m,
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    (forall i, indom (fsi2 m) i -> hv[`k](i) = hv'[`k](i)) ->
    op hv m = op hv' m) ->
  (i <> j) -> (j <> k) -> (k <> i) ->
  (Z <= N)%Z ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (Pre ==> 
    Inv b0 Z \* 
    (\*_(d <- Union `[Z,N] fsi1) R1 d) \*
    (\*_(d <- Union `[Z,N] fsi2) R2 d) \*
    p ~⟨(i, 0%Z), s⟩~> val_int 0) ->
  (forall hv, 
    Inv false N \* 
    (\*_(d <- Union `[Z,N] fsi1) R1' d) \*
    (\*_(d <- Union `[Z,N] fsi2) R2' d) \* 
    p ~⟨(i, 0%Z), s⟩~> val_int (Σ_(i <- interval Z N) (op hv i)) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => While C T};
      {j| ld in Union `[Z,N] fsi1 => C1 ld};
      {k| ld in Union `[Z,N] fsi2 => C2 ld}
    }]
  {{ hv, Post hv }}.
Proof.
  move=> IHT IHF IHC IHN Dj1 Dj2 opP iNj jNk kNi ??????? PreH PostH.
  rewrite /ntriple /nwp ?fset_of_cons /= union_empty_r.
  eapply wp_while with
    (C := C)
    (fsi := fun d => ⟨(j,0), fsi1 d⟩ \u ⟨(k,0), fsi2 d⟩ )
    (H:=(fun b q hv => 
      Inv b q \* 
      (\*_(d <- Union `[Z,q] fsi1) R1' d) \*
      (\*_(d <- Union `[q,N] fsi1) R1  d) \* 
      (\*_(d <- Union `[Z,q] fsi2) R2' d) \*
      (\*_(d <- Union `[q,N] fsi2) R2  d) \* 
      p ~⟨(i, 0%Z), s⟩~> Σ_(l <- interval Z q) op hv l))
    (hv0:=fun=> 0)=> //; try eassumption.
  { move=> r b hv hv' hvE.
    suff->:
      Σ_(l <- interval Z r) op hv l = 
      Σ_(l <- interval Z r) op hv' l by xsimpl.
    apply/SumEq=> *; apply/opP=> *; apply/hvE.
    all: rewrite indom_Union; eexists; rewrite indom_union_eq ?indom_label_eq; autos*. }
  { rewrite ?[_ Z Z]intervalgt; try math.
    rewrite ?Union0 ?hbig_fset_empty ?Sum0. xsimpl*. }
  { move=> ?.
    rewrite ?[_ N N]intervalgt; try math.
    rewrite ?Union0 ?hbig_fset_empty. xsimpl*. }
  { simpl; clear -iNj jNk kNi Dj1 Dj2.
    intros; rewrite ?disjoint_union_eq_l ?disjoint_label; do ? split; try by (left=> -[]//; lia).
    { right; exact/Dj1. }
    right; exact/Dj2. }
  { clear -iNj jNk kNi Dj1 Dj2.
    rewrite ?Union_label Union_union // => ??; 
    rewrite ?indom_interval ?disjoint_eq_label; eauto.
    rewrite disjoint_label; left; by case. }
  { rewrite label_single; reflexivity. }
  { move=> ?? /=; rewrite indom_union_eq ?indom_label_eq=> -[][]; eqsolve. }
  { rewrite /htrm_of /=; case: classicT=> //=> []; split*. }
  { clear -IHC Dj1 Dj2 iNj jNk kNi opP.
    move=> hv l b /IHC-/(_ b).
    rewrite /ntriple/nwp ?fset_of_cons /= ?fset_of_nil union_empty_r.
    rewrite /htrm_of label_single wp_single /= indom_single_eq.
    do ? case: classicT; autos*=> _.
    rewrite -wp_equiv wp_equiv=> HT; xapp; xsimpl*. }
  { move=> ??. xchange IHN; xsimpl*. }
  { clear -IHT Dj1 Dj2 iNj jNk kNi opP.
    move=> l hv /[dup]?/IHT. 
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
    rewrite union_empty_r ?intervalUr; try lia.
    rewrite ?Union_upd //; first last. 
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj1=> //; math. }
      move=> ? [?|?]; subst; apply/Dj1; math. }
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj2=> //; math. }
      move=> ? [?|?]; subst; apply/Dj2; math. }
    rewrite ?hbig_fset_union; first last; eauto; try by (hnf; auto).
    { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj1; math. }
    { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj2; math. }
    rewrite (@intervalU l N); try math.
    rewrite ?Union_upd //; first last.
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj1=> //; math. }
      move=> ? [?|?]; subst; apply/Dj1; math. }
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj2=> //; math. }
      move=> ? [?|?]; subst; apply/Dj2; math. }
    rewrite ?hbig_fset_union; first last; eauto; try by (hnf; auto).
    { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj1; math. }
    { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj2; math. }
    setoid_rewrite wp_equiv at 1=> Hwp.
    erewrite wp_ht_eq with (ht2:=(htrm_of
      ((Lab (pair i 0) (FH (single s tt) (fun=> T))) ::
        (Lab (pair j 0) (FH (fsi1 l) (fun ld => C1 ld))) ::
         (Lab (pair k 0) (FH (fsi2 l) (fun ld => C2 ld))) ::
        nil))).
    2:{ intros (ll, d) H. unfold upd, htrm_of. simpl. 
      rewrite ?indom_union_eq ?indom_label_eq in H.
      rewrite indom_single_eq in H |- *.
      repeat case_if; try eqsolve.
      { destruct C6 as (<- & HH); false C4. split; auto.
        rewrite indom_Union. exists l. rewrite indom_interval.
        split; try math; auto. }
      destruct C7 as (<- & HH); false C5. split; auto.
      rewrite indom_Union. exists l. rewrite indom_interval.
      split; try math; auto. }
    xapp=> {}hr ?; xsimpl.
    rewrite <- intervalUr; try math. rewrite SumxSx; try math.
    move=> ?; apply:applys_eq_init. 
    do 3 f_equal; [apply/SumEq=> ??|]; apply/opP=> ? IN*; 
    rewrite /uni indom_Union; case: classicT=> //.
    { case; eexists; splits*; rewrite indom_union_eq ?indom_label_eq; autos*. }
    { case; eexists; splits*; rewrite indom_union_eq ?indom_label_eq; autos*. }
    { case=> l' []/[!indom_union_eq]/[!@indom_label_eq]/[!indom_interval]=> ?.
      case=> [[]_|[][]//]; last eqsolve.
      move=>/disjoint_inv_not_indom_both /(_ IN)-[].
      apply/Dj1; lia. }
    case=> l' []/[!indom_union_eq]/[!@indom_label_eq]/[!indom_interval]=> ?.
    case=> [[][]//|[]_].
    move=>/disjoint_inv_not_indom_both /(_ IN)-[].
    apply/Dj2; lia. }
  clear -IHF Dj1 Dj2 iNj jNk kNi opP.
  move=> l hv /[dup]?/IHF. 
  rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
  rewrite union_empty_r ?intervalUr; try lia.
  rewrite ?Union_upd //; first last. 
  { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
    case=> [?[?|]|]; first by subst.
    { subst=> ?; apply/Dj1=> //; math. }
    move=> ? [?|?]; subst; apply/Dj1; math. }
  { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
    case=> [?[?|]|]; first by subst.
    { subst=> ?; apply/Dj2=> //; math. }
    move=> ? [?|?]; subst; apply/Dj2; math. }
  rewrite ?hbig_fset_union; first last; eauto; try by (hnf; auto).
  { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj1; math. }
  { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj2; math. }
  rewrite (@intervalU l N); try math.
  rewrite ?Union_upd //; first last.
  { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
    case=> [?[?|]|]; first by subst.
    { subst=> ?; apply/Dj1=> //; math. }
    move=> ? [?|?]; subst; apply/Dj1; math. }
  { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
    case=> [?[?|]|]; first by subst.
    { subst=> ?; apply/Dj2=> //; math. }
    move=> ? [?|?]; subst; apply/Dj2; math. }
  rewrite ?hbig_fset_union; first last; eauto; try by (hnf; auto).
  { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj1; math. }
  { rewrite disjoint_Union=> ? /[! indom_interval] ?; apply/Dj2; math. }
  setoid_rewrite wp_equiv at 1=> Hwp.
  erewrite wp_ht_eq with (ht2:=(htrm_of
      ((Lab (pair j 0) (FH (fsi1 l) (fun ld => C1 ld))) ::
         (Lab (pair k 0) (FH (fsi2 l) (fun ld => C2 ld))) ::
        nil))).
  2:{ intros (ll, d) H. unfold upd, htrm_of. simpl. 
    rewrite ?indom_union_eq ?indom_label_eq in H.
    rewrite indom_single_eq in H |- *.
    repeat case_if; try eqsolve.
    { destruct C5 as (<- & HH); false C3. split; auto.
      rewrite indom_Union. exists l. rewrite indom_interval.
      split; try math; auto. }
    destruct C6 as (<- & HH); false C4. split; auto.
    rewrite indom_Union. exists l. rewrite indom_interval.
    split; try math; auto. }
  xapp=> {}hr; xsimpl.
  rewrite <- intervalUr; try math. rewrite SumxSx; try math.
  move=> E0 ?; apply:applys_eq_init. 
  do 2 f_equal; rewrite (opP _ hr) ?E0 ?Z.add_0_r;
  [apply/SumEq=> ??; apply/opP| |]=> ? IN*; rewrite /uni indom_Union; case: classicT=> //.
  { case; eexists; splits*; rewrite indom_union_eq ?indom_label_eq; autos*. }
  { case; eexists; splits*; rewrite indom_union_eq ?indom_label_eq; autos*. }
  { case=> l' []/[!indom_union_eq]/[!@indom_label_eq]/[!indom_interval]=> ?.
    case=> [[]_|[][]//]; last eqsolve.
    move=>/disjoint_inv_not_indom_both /(_ IN)-[].
    apply/Dj1; lia. }
  case=> l' []/[!indom_union_eq]/[!@indom_label_eq]/[!indom_interval]=> ?.
  case=> [[][]//|[]_].
  move=>/disjoint_inv_not_indom_both /(_ IN)-[].
  apply/Dj2; lia.
Qed.

Lemma xfor_big_op_lemma_aux `{INH: Inhab D} {A B : Type} Inv (R R' : Dom -> hhprop) 
	(toval : A -> val) (a0 : A) (bdef : B) (fa : A -> B -> A) (Pb : B -> Prop)
  (op : (D -> val) -> int -> B) p
  s fsi1 vr
  Z N (C1 : Dom -> trm) (i j : int) (C : trm)
  Pre Post: 
  (forall (l : int) (a : A), 
    Z <= l < N ->
    {{ Inv l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R d) \* 
       p ~⟨(i, 0%Z), s⟩~> (toval a)}}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' d) \* 
        p ~⟨(i, 0%Z), s⟩~> (toval (fa a (op hv l))) \*
        \[Pb (op hv l)] }}) ->
  (forall i0 j0 : int, i0 <> j0 -> Z <= i0 < N -> Z <= j0 < N -> disjoint (fsi1 i0) (fsi1 j0)) ->
  (forall (hv hv' : D -> val) m,
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    Z <= m < N ->
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
    p ~⟨(i, 0%Z), s⟩~> (toval a0)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi1) R' d) \* 
    p ~⟨(i, 0%Z), s⟩~> (toval (fold_left fa (projT1 (list_of_fun' (fun i => op hv (i + Z)) (N - Z))) a0)) \*
    \[forall i, Z <= i < N -> Pb (op hv i)] ==>
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
      p ~⟨(i, 0%Z), s⟩~> (toval (fold_left fa (projT1 (list_of_fun' (fun i => op hv (i + Z)) (q - Z))) a0)) \*
      \[forall i, Z <= i < q -> Pb (op hv i)]))
    (hv0:=fun=> 0)=> //; try eassumption.
  { clear -bdef IH Dj iNj opP.
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
    specialize (Hwp (fold_left fa (projT1 (list_of_fun' (fun i => op hv (i + Z)) (l - Z))) a0) Htmp). clear Htmp.
    xsimpl. intros Hpb.
    apply wp_equiv in Hwp. apply wp_equiv.
    eapply htriple_conseq_frame.
    1: apply Hwp.
    1: xsimpl. 1: xsimpl.
    hnf. intros v. xsimpl.
    1:{ intros Hpb0 i0 Hi0.  
      destruct (Z.ltb i0 l) eqn:E.
      (* TODO this proof is repeating below *)
      { apply Z.ltb_lt in E. rewrite <- opP with (hv:=hv); try math. 1: apply Hpb; math.
        intros i1 Hi1. unfold uni. rewrite /uni indom_label_eq. case_if; auto.
        destruct C0 as (_ & Hin2).
				false @disjoint_inv_not_indom_both. 2: apply Hi1. 2: apply Hin2.
				apply Dj; math. }
      { apply Z.ltb_ge in E. assert (i0 = l) as -> by math. rewrite <- opP with (hv:=v); try math; try assumption.
        intros i1 Hi1. unfold uni. rewrite /uni indom_label_eq. case_if; eqsolve. } }
    intros Hpb0. xsimpl. clear Hwp.
		destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
		destruct (list_of_fun' _ _) as (l2 & Hlen2 & Hl2); simpl.
		match goal with 
			|- _ ==> ?a => eapply eq_ind_r with (y:=a)
		end; [ xsimpl* | ].
		do 2 f_equal.  
		enough (l2 = List.app l1 (op v l :: nil)) by (subst; now rewrite fold_left_app).
		apply (List.nth_ext _ _ bdef bdef).
		{ rewrite List.app_length /=. math. }
		{ intros n Hlt. 
			destruct (Nat.ltb n (Datatypes.length l1)) eqn:E.
			{ apply Nat.ltb_lt in E. rewrite app_nth1; try math.
				replace n with (abs n)%nat by math.
				rewrite -> Hl1, -> Hl2; try math. apply opP; try math.
				intros i0 Hin. rewrite /uni indom_label_eq. case_if; auto.
				destruct C0 as (_ & Hin2).
				false @disjoint_inv_not_indom_both. 2: apply Hin. 2: apply Hin2.
				apply Dj; math. }
			{ apply Nat.ltb_ge in E. 
				assert (n = Datatypes.length l1) as En by math. 
				rewrite -> En at 2. rewrite -> nth_middle.
				replace n with (abs n)%nat by math.
				rewrite -> Hl2; try math. replace (n+Z) with l by math. apply opP; try math.
				intros i0 Hin. rewrite /uni indom_label_eq. case_if; eqsolve. } } }
  { move=> r hv hv' ? hvE.
    do 4 f_equal.
    2:{ f_equal. extens. split; intros H i0 Hi0. 
      1: erewrite <- opP with (hv:=hv); try apply H; try math.
      2: erewrite -> opP with (hv':=hv'); try apply H; try math.
      all: intros i1 Hi1; apply hvE.
      all: rewrite indom_Union; exists i0; indomE; split; [ math | auto ]. }
    suff->:
			projT1 (list_of_fun' (fun i0 : int => op hv (i0 + Z)) (r - Z)) = 
      projT1 (list_of_fun' (fun i0 : int => op hv' (i0 + Z)) (r - Z)) by xsimpl.
		destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
		destruct (list_of_fun' _ _) as (l2 & Hlen2 & Hl2); simpl.
		apply (List.nth_ext _ _ bdef bdef). 1: math.
		intros n Hlt. replace n with (abs n)%nat by math.
		rewrite -> Hl1, -> Hl2; try math. 
    apply/opP=> // *; try lia. apply/hvE.
    rewrite indom_Union; exists (n+Z); indomE. split; [ math | auto ]. }
  { rewrite [_ Z Z]intervalgt; last math.
		rewrite Union0 hbig_fset_empty. 
		destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
		replace (abs _) with 0%nat in Hlen1 by math. destruct l1; try discriminate; xsimpl.
    intros; math. }
  { move=> ?.
    rewrite [_ N N]intervalgt; last math.
    rewrite Union0 hbig_fset_empty. xsimpl*. }
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
    simpl in H. rewrite indom_label_eq indom_single_eq in H0.  
    destruct H0; subst.
    rewrite indom_label_eq in H.
    eqsolve.
  }
  by case=> l d; rewrite indom_label_eq /= /htrm_of; case: classicT.
Qed.

Lemma lab_eqbE l1 l2: 
  (lab_eqb l1 l2) = (l1 = l2) :> Prop.
Proof. by extens; split=> [/lab_eqbP|->]// /[! eqbxx]. Qed.

Lemma ntriple_sequ2_gen (fs : fset _) H Q' Q fsht
  (ht1 ht2 : _ -> trm) (i : int)
  (Htppre : 
    ntriple H
      (Lab (pair i 0) (FH fs ht1) :: 
       fsht)
    Q')
  (Htp2 : forall hv, 
    htriple (label (Lab (pair i 0) fs)) (fun d => ht2 (eld d)) 
      (Q' hv) (fun hr => Q (uni (fset_of fsht) hv hr)))
  :
  ~ has_lab fsht (i,0) ->
  ntriple H
    (Lab (pair i 0) (FH fs (fun d => trm_seq (ht1 d) (ht2 d))) :: 
    fsht)
    Q.
Proof using.
  (* move/hasnt_lab. *)
  move=> HNL.
  unfold ntriple, nwp.
  simpl fset_of.
  erewrite -> wp_ht_eq.
  1: apply wp_equiv.
  1: eapply htriple_sequ2 with 
    (ht1:=fun d => ht1 (eld d))
    (ht2:=fun d => ht2 (eld d))
    (htpre:=uni (label (Lab (pair i 0) fs)) (fun d => ht1 (eld d))
      (htrm_of fsht))
    (ht:=uni (label (Lab (pair i 0) fs)) (fun d => trm_seq (ht1 (eld d)) (ht2 (eld d)))
      (htrm_of fsht))
    (ht':=htrm_of fsht).
  { rewrite (hasnt_lab _ _ HNL); exact/fset_htrm_label_remove_disj. }
  { intros. unfold uni. case_if; try reflexivity. contradiction. }
  { move=> ?; rewrite (hasnt_lab _ _ HNL) /uni; case: classicT=> //.
    move=>/disjoint_inv_not_indom_both/[apply]-[].
    exact/fset_htrm_label_remove_disj. }
  2:{
    intros. unfold uni. case_if; try reflexivity. contradiction.
  }
  2:{ move=> ?; rewrite (hasnt_lab _ _ HNL) /uni; case: classicT=> //.
    move=>/disjoint_inv_not_indom_both/[apply]-[].
    exact/fset_htrm_label_remove_disj. }
  3:{ case=> *; by rewrite /uni /= indom_label_eq. }
  2: apply Htp2.
  unfold ntriple, nwp in Htppre.
  simpl fset_of in Htppre.
  apply wp_equiv.
  erewrite -> wp_ht_eq in Htppre.
  1: apply Htppre.

  intros. destruct d as (ll, d).
  rewrite -> indom_union_eq, -> ! indom_label_eq in H0. 
  unfold htrm_of, uni. rewrite ! indom_label_eq. simpl. repeat case_if; try eqsolve.
Qed.

Lemma xwhile_big_op_lemma2 `{INH: Inhab D} Inv (R1 R2 R1' R2' : Dom -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1 fsi2
  Z N (C1 C2 : Dom -> trm) (i j k : int) (C C' T : trm) b0
  Pre Post: 
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv true l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R1 d) \* 
       (\*_(d <- ⟨(k, 0%Z), fsi2 l⟩) R2 d) \* 
       p ~⟨(i, 0%Z), s⟩~> (val_int x) }}
      [{
        {i| _  in `{s}  => T};
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ hv, \exists b,
        Inv b (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R1' d) \*
        (\*_(d <- ⟨(k, 0%Z), fsi2 l⟩) R2' d) \* 
        p ~⟨(i, 0%Z), s⟩~> (val_int (x + (op hv l))) }}) ->
  (forall (l : int) (x : int), 
    Z <= l < N ->
    {{ Inv false l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R1 d) \*
        \*_(d <- ⟨(k, 0%Z), fsi2 l⟩) R2 d }}
      [{
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ hv, \[op hv l = 0] \*
        Inv false (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R1' d) \* 
         \*_(d <- ⟨(k, 0%Z), fsi2 l⟩) R2' d}}) ->
  (forall (l : int) (b : bool), 
    Z <= l <= N ->
    {{ Inv b l }}
      [{
        {i| _  in `{s}  => C}
      }]
    {{ hv, \[hv[`i](s) = b] \* Inv b l }}) ->
  (forall b, Inv b N ==> \[b = false] \* Inv b N) ->
  (forall i j : int, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi1 i) (fsi1 j)) ->
  (forall i j : int, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi2 i) (fsi2 j)) ->
  (forall (hv hv' : D -> val) m,
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    (forall i, indom (fsi2 m) i -> hv[`k](i) = hv'[`k](i)) ->
    op hv m = op hv' m) ->
  (i <> j) -> (j <> k) -> (k <> i) ->
  (Z <= N)%Z ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (Pre ==> 
    Inv b0 Z \* 
    (\*_(d <- Union `[Z,N] fsi1) R1 d) \*
    (\*_(d <- Union `[Z,N] fsi2) R2 d) \*
    p ~⟨(i, 0%Z), s⟩~> val_int 0) ->
  (forall hv, 
    Inv false N \* 
    (\*_(d <- Union `[Z,N] fsi1) R1' d) \*
    (\*_(d <- Union `[Z,N] fsi2) R2' d) \* 
    p ~⟨(i, 0%Z), s⟩~> val_int (Σ_(i <- interval Z N) (op hv i)) ==>
      wp ⟨(i,0), `{s}⟩ (fun=> C') (fun hr => Post (lab_fun_upd hr hv (i,0)))) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => trm_seq (While C T) C'};
      {j| ld in Union `[Z,N] fsi1 => C1 ld};
      {k| ld in Union `[Z,N] fsi2 => C2 ld}
    }]
  {{ hv, Post hv }}.
Proof.
  move=> ?????????????????? PostH.
  eapply ntriple_sequ2_gen with (Q' := fun hv=> Inv false N \*
    (\*_(d <- \U_(i <- `[Z, N]) fsi1 i) R1' d) \*
    (\*_(d <- \U_(i <- `[Z, N]) fsi2 i) R2' d) \*
    p ~⟨(i, 0%Z), s⟩~> (Σ_(i <- `[Z, N]) op hv i)); autos*=> /=.
  { apply/xwhile_big_op_lemma_aux2; try eassumption; xsimpl*. }
  { move=> v; rewrite -wp_equiv; apply: himpl_trans_r.
    apply/wp_hv; apply: wp_conseq Hwp=> hr ? Qh.
    setoid_rewrite wp_equiv in PostH; xapp=> hr.
    xsimpl (lab_fun_upd hr v (i, 0))=> ?; apply:applys_eq_init; f_equal; extens=> -[??].
    rewrite /uni; case: classicT.
    { rewrite union_empty_r indom_union_eq ?indom_label_eq.
      case: ssrbool.ifP=> //. 
      rewrite /is_true bool_eq_true_eq lab_eqbE /==>->[][][]; eqsolve. } 
    rewrite indom_label_eq indom_single_eq. 
    by case: classicT=> // -[]<-<-/= /[! eqbxx]. }
  rewrite Bool.orb_false_r.
  case E: (lab_eqb _ _); move: E=> /=.
  { move<-. rewrite lab_eqbE. eqsolve. }
  rewrite lab_eqbE. eqsolve.
Qed.

Lemma xfor_big_op_lemma `{Inhab D} {A B : Type} Inv (R R' : Dom -> hhprop) 
	(toval : A -> val) (a0 : A) (bdef : B) (fa : A -> B -> A) (Pb : B -> Prop)
  (op : (D -> val) -> int -> B) p 
  s fsi1 vr
  Z N (C1 : Dom -> trm) (i j : int) (C : trm) C'
  Pre Post: 
  (forall (l : int) (a : A), 
    Z <= l < N ->
    {{ Inv l \* 
       (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R d) \* 
       p ~⟨(i, 0%Z), s⟩~> (toval a) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ hv, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j, 0%Z), fsi1 l⟩) R' d) \* 
        p ~⟨(i, 0%Z), s⟩~> (toval (fa a (op hv l))) \*
        \[Pb (op hv l)] }}) ->
  (forall i j : int, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi1 i) (fsi1 j)) ->
  (forall (hv hv' : D -> val) m,
     Z <= m < N ->
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
    p ~⟨(i, 0%Z), s⟩~> (toval a0)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi1) R' d) \* 
    p ~⟨(i, 0%Z), s⟩~> (toval (fold_left fa (projT1 (list_of_fun' (fun i => op hv (i + Z)) (N - Z))) a0)) \*
    \[forall i, Z <= i < N -> Pb (op hv i)] ==>
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
  apply/(@xunfocus_lemma _ (fun hr => WP [ _ in ⟨(i, 0), single s tt⟩  => C' ]
  { hr'0, Post ((hr \u_ ⟨(j, 0), Union (interval Z N) fsi1⟩) hr'0) }))=> /=; autos*.
  { by rewrite E. }
  move=> ??; fequals; apply/fun_ext_1=> ?. fequals.
  extens=> -[]??; rewrite /uni; case: classicT=> //.
  xfocus (i,0); rewrite ?eqbxx lab_eqb_sym E /=.
  apply/xunfocus_lemma; autos*=> /=.
  { by rewrite lab_eqb_sym E. }
  { move=> ??. remember ((_ \u_ _) _); reflexivity. }
  simpl.
  apply/(xfor_big_op_lemma_aux Inv R R' toval a0 bdef); eauto.
  move=> hv. apply: himpl_trans; [|apply/wp_hv].
  move: (H12 hv); rewrite wp_equiv=> ?.
  xapp=> //. move=> Hpb hv'. rewrite -/(lab_fun_upd _ _ _).
  xsimpl (lab_fun_upd hv' hv (i, 0))=> ?.
  apply: applys_eq_init; fequals; apply/fun_ext_1=> /=.
  case=> l x.
  rewrite /uni ?indom_label_eq; case: classicT.
  { by case=> <- /=; rewrite lab_eqb_sym E. }
  case: classicT=> //.
  case=> <- /=; rewrite eqbxx //.
Qed.

Lemma xfor_big_op_lemma_int `{Inhab D} Inv (R R' : Dom -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1 vr
  Z N (C1 : Dom -> trm) (i j : int) (C : trm) C'
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
     Z <= m < N ->
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
  apply/(xfor_big_op_lemma Inv R R' val_int 0 0 Z.add (fun=> True)); eauto.
  1:{ intros. eapply himpl_trans. 1: apply H0; try assumption. apply wp_conseq. xsimpl*. }
	intros. eapply himpl_trans. 2: apply H12; try assumption. xsimpl=>_.
	match goal with
		|- context[fold_left Z.add ?ll 0] => eapply eq_ind_r with (y:=fold_left Z.add ll 0)
	end; [ xsimpl* | ].
	destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
	rewrite -> Sum_interval_change with (c:=(-Z)).
	replace (`[_, _]) with (`[0, N - Z]) by (f_equal; math).
	replace (N - Z) with (Z.of_nat (List.length l1))%Z in Hl1 |- * by math.
	erewrite SumEq with (G:=fun i0 => l1[i0]). 
	2: intros i0; indomE; intros Hi0; rewrite Hl1; try math; f_equal; math.
	by rewrite -> SumList_fold_eq'.
Qed.

Lemma xfor_lemma2_hbig_op `{ID : Inhab D}
  Inv 
  (R1 R1' R2 R2' : Dom -> hhprop)
  m vd (H : int -> hhprop) (H' : int -> (D -> val) -> hhprop)
  s fsi1 fsi2 vr
  (N: Z) (C1 C2 : Dom -> trm) (C : trm)
  (i j k : Z)
  Pre Post: 
  (forall (l : int) Q, 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1 d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2 d) \* 
        Q \(m, vd) H l }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1' d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2' d) \* 
        Q \(m, vd) H' l v }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall j : int, hlocal (H j) ⟨(i,0%Z), single s tt⟩) ->
  (forall (j : int) (v : D -> val), hlocal (H' j v) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R1 i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R1' i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R2 i) ⟨(k,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R2' i) ⟨(k,0%Z), single i tt⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    (forall i, indom (fsi2 m) i -> hv[`k](i) = hv'[`k](i)) ->
    H' m hv = H' m hv') ->
  comm m -> assoc m -> (forall x y, (vd x /\ vd y) <-> vd (m x y)) ->
  (i <> j)%Z ->
  (j <> k)%Z ->
  (k <> i)%Z ->
  0 <= N ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R1 d) \*
    (\*_(d <- Union `[0,N] fsi2) R2 d) \*
    \(m, vd)_(i <- `[0,N]) H i) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R1' d) \* 
    (\*_(d <- Union `[0,N] fsi2) R2' d) \* 
    (\(m, vd)_(i <- `[0,N]) H' i hv) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For 0 N (trm_fun vr C)};
      {j| ld in Union `[0,N] fsi1 => C1 ld};
      {k| ld in Union `[0,N] fsi2 => C2 ld}
    }]
  {{ v, Post v }}. 
Proof.
  move=> IH lI lH lH' lR1 lR1' lR2 lR2' opP CM AS VM iNj jNk kNi N0 ? ??? ?? PreH PostH.
  rewrite /ntriple /nwp ?fset_of_cons /= union_empty_r.
  set (f := (fun '(Lab (p, q) x) => Lab 
    (If p = j then 
      If  0 <= q < N /\ indom (fsi1 q) x then (j,0)%Z else (p, 2 * (q + N) + 1)
    else If p = k then 
      If  0 <= q < N /\ indom (fsi2 q) x then (k,0)%Z else (p, 2 * (q + N) + 1)
    else (p, q)) 
    x) : D -> D).
  set (g := (fun '(Lab (p, q) x) => Lab 
    (If p = j then 
      If q = 0 /\ indom (Union (interval 0 N) fsi1) x then
        (j, Get 0 N fsi1 x)
      else (j, -1)
    else If p = k then 
      If q = 0 /\ indom (Union (interval 0 N) fsi2) x then
        (k, Get 0 N fsi2 x)
      else (k, -1)
    else (p, q)) x)).
  set (fi (i : int) := (fun '(Lab (p, q) x) => If p = j \/ p = k then Lab (p, q - i) x else Lab (p, q) x) : D -> D).
  set (gi (i : int) := (fun '(Lab (p, q) x) => If p = j \/ p = k then Lab (p, q + i) x else Lab (p, q) x) : D -> D).
  set (fsi' (i : int) := ⟨(j, i), fsi1 i⟩ \u ⟨(k, i), fsi2 i⟩).
  have H'E :forall hv, 
    \(m, vd)_(i <- `[0,N]) H' i hv = \(m, vd)_(i <- `[0,N]) H' i (hv \o f \o set2 i).
  { move=> hv; apply/hbig_fset_eq=> d /[dup]?; rewrite indom_interval=>?.
    apply/opP=> // x ? /=; case: classicT=> // ; try lia.
    { by case: classicT=> // -[]; split=> //; rewrite -indom_interval. }
    case: classicT=> // _ ?; case: classicT=> // -[].
    by split=> //; rewrite -indom_interval. }
  (set r := fun d => if lab_eqb (lab d) (j,0) then R1 (el d) else if lab_eqb (lab d) (k,0) then R2 (el d) else \[]).
  (set r' := fun d => if lab_eqb (lab d) (j,0) then R1' (el d) else if lab_eqb (lab d) (k,0) then R2' (el d) else \[]).
  have lbE1: (lab_eqb (k,0) (j,0) = false).
  { rewrite /lab_eqb /=. case E: (k =? j)=> //.  lia. }
  have lbE2: (lab_eqb (j,0) (k,0) = false).
  { rewrite /lab_eqb /=. case E: (j =? k)=> //.  lia. }
  apply/(
    wp_for_hbig_op_na_bis Inv 
      r
      r'
      H (fun i hv => H' i (hv \o set2 i))  
      (fun d => ⟨(j,0%Z), fsi1 d⟩ \u ⟨(k,0%Z), fsi2 d⟩) Post fsi' fi gi g
      (fs' := ⟨(i, 0), single s tt⟩)
      (fs := ⟨(j, 0), \U_(i <- `[0, N]) fsi1 i⟩ \u ⟨(k, 0), \U_(i <- `[0, N]) fsi2 i⟩)
      (f := f)
      (* (fsi' := fsi') *)
  ); try eassumption.
  { rewrite /r/r' -Union_union_fset hbig_fset_union //.
      { rewrite -?Union_label ?hstar_fset_Lab /= ?eqbxx lbE1; xsimpl*. }
      do 2 rewrite disjoint_Union=> ??. 
      rewrite disjoint_label. left=> -[]. lia. }
  { by rewrite -Union_union_fset ?Union_label. }
  { by case=> l d; rewrite indom_label_eq /= /htrm_of; case: classicT. }
  { by move=> *. }
  { case=> ??; rewrite /r /=; do ? case: ssrbool.ifP.
    1,2: move/lab_eqbP->; rewrite -label_single; autos*.
    move=> *; exact/hlocal_hempty. }
  { case=> ??; rewrite /r' /=; do ? case: ssrbool.ifP.
    1,2: move/lab_eqbP->; rewrite -label_single; autos*.
    move=> *; exact/hlocal_hempty. }
  { clear. move=> ? [][??]?; rewrite /gi /fi.
    (do ? case: classicT=> //)=> -[]-> _; do ? fequals; lia. }
  { clear. move=> ? [][??]?; rewrite /gi /fi.
    (do ? case: classicT=> //)=> -[]-> _; do ? fequals; lia. }
  { clear. move=> i; rewrite /fi /fsi'; clear.
    apply/fset_extens=> -[][] l1 l2 x.
    rewrite indom_fsubst; split; rewrite ?indom_union_eq ?indom_label_eq.
    { case=> -[][]m1 m2 y; rewrite ?indom_union_eq ?indom_label_eq.
      case: classicT=> [[]->|/[swap] ] [][]-><-->[][][]; do ? move->.
      all: try (left; split=> //; fequals; lia).
      all: right; split=> //; fequals; lia. }
    case=> -[][]-><- ?.
    all: exists (Lab (l1, i) x); case: classicT=> //; rewrite ?indom_union_eq ?indom_label_eq.
    all: try lia.
    all: move=> ?; split; try (do ? fequals; lia).
    { by left. }
    by right. }
  { rewrite /fsi' /f /fi; clear -iNj jNk kNi.
     move=> ? [][]l1 l2 x; rewrite ?indom_union_eq ?indom_label_eq.
    rewrite indom_interval=> /[swap]; case=> -[][]<-->??.
    all: case: classicT=> // ?; try lia.
    2: case: classicT=> // _.
    all: case: classicT=> // [|[] ] // _.
    all: case: classicT=> ?; try lia.
    all: do ? fequals; lia. }
  { rewrite /f /fsi' /Fs; clear -N0 iNj jNk kNi=> -[][]l1 l2 x[][]m1 m2 y ?.
    have ?: (~ (l1 = m1 /\ l2 = m2 /\ x = y)).
    { case=> ?[]??; by subst. }
    do ? case:classicT=> //.
    { case=> ??->[]??->[]?. rewrite -Union_union_fset ?indom_union_eq ?indom_Union.
      split; [left; exists l2|left; exists m2]; by rewrite indom_interval indom_label_eq. }
    all: try (move=> ????? []; lia).
    all: try (move=> ???? []; lia).
    { move=> ???? []*; subst. have?: l2 = m2 by (lia). by subst. }
    { case=> ??->?[]??->?[]?. rewrite -Union_union_fset ?indom_union_eq ?indom_Union.
      split; [right; exists l2|right; exists m2]; by rewrite indom_interval indom_label_eq. }
    all: try (move=> ?????? []*; subst; lia).
    move=> ?????? []*; have?: l2 = m2 by (lia). by subst. }
  { case=> -[]l1 l2 x; clear -iNj jNk kNi.
    split.
    { rewrite indom_fsubst=> -[][][]m1 m2 y[] /[swap].
      rewrite indom_union_eq=> -[].
      { rewrite indom_label_eq indom_single_eq=> -[][]<-<-<-.
        rewrite /f. do 2 case: classicT=> //; try lia. 
        move=> ?? []<-<-<-.
        rewrite /g; do 2 case: classicT=> // _.
        rewrite indom_union_eq indom_label_eq indom_single_eq; by left. }
      rewrite /Fs indom_Union /fsi'=> -[r][]. 
      rewrite ?indom_union_eq ?indom_label_eq ?indom_interval=> I [][][].
      { move=> <- <- ind; rewrite /f; case: classicT=> //.
        case: classicT=> [|[] ] // _ _ []<-<-<-.
        case: classicT=> //.
        rewrite indom_single_eq; right.
        rewrite /g; case: classicT=> //.
        case: classicT.
        { move=> _ _; rewrite indom_Union; exists (Get 0 N fsi1 y).
          rewrite indom_union_eq ?indom_label_eq.
          case: (Get_in _ I ind); do ? split=> //; by left. }
        case; split=> //; rewrite indom_Union; exists r.
        split=> //; by rewrite indom_interval. }
      move=> <- <- ind; rewrite /f; case: classicT=> //; try lia.
      case: classicT=> // ??.
      case: classicT=> [|[] ] // _ []<-<-<-.
      case: classicT=> //.
      rewrite indom_single_eq; right.
      rewrite /g; case: classicT=> //.
      case: classicT=> //.
      move=> _ _; rewrite indom_Union; exists (Get 0 N fsi2 y).
      rewrite indom_union_eq ?indom_label_eq.
      case: classicT=> [|[] ]; last split=> //.
      { case: (Get_in _ I ind); do ? split=> //; by right. }
      rewrite indom_Union; exists r; by rewrite indom_interval. }
    rewrite indom_union_eq=> -[].
    { rewrite /g; (do ? case: classicT)=> [??|??|???|???|]; rewrite indom_label_eq.
      1-4: move=> -[][]; lia.
      move=> ?? [][]<-<- ?.
      rewrite indom_fsubst; exists (⟨(i, 0), x⟩)%arr; split.
      { rewrite /f; do 2 case: classicT=> //; lia. }
      by rewrite indom_union_eq; left; rewrite indom_label_eq. }
    rewrite /Fs indom_Union=> -[]r[]/[dup]?.
    rewrite indom_interval=> ?.
    rewrite /fsi' /g; case: classicT=> [->|].
    { case: classicT.
      { case=> -> ?.
        rewrite indom_union_eq ?indom_label_eq=> -[][][]; last lia.
        move=> ??.
        rewrite indom_fsubst; exists (Lab (j, r) x); split.
        { rewrite /f; case: classicT=> // _.
          case: classicT=> // -[] //. }
        rewrite indom_union_eq indom_Union; right.
        exists r; rewrite indom_union_eq ?indom_label_eq; split=>//.
        by left. }
      move=> _; rewrite indom_union_eq ?indom_label_eq=> -[][][]; lia. }
    move=> ?; rewrite indom_union_eq ?indom_label_eq=> -[][].
    { do ? case: classicT.
      { case=> -> ? -> []; lia. }
      { move=> ?? []; lia. }
      move=> ? []; lia. }
    do ? case: classicT.
    { case=> -> ? -> [] ??.
      rewrite indom_fsubst; exists (Lab (k, r) x); split.
      { rewrite /f; case: classicT=> //; first lia.
        case: classicT=> // ??.
        by case: classicT=> // -[]. }
      rewrite indom_union_eq indom_Union; right.
      exists r; rewrite indom_union_eq ?indom_label_eq; split=>//.
      by right. }
    { move=> ?? []; lia. }
    move=> ? []; lia. }
  { case=> -[]l1 l2 x; clear -iNj jNk kNi.
    rewrite ?indom_union_eq=> -[]; rewrite ?indom_label_eq=> -[][][]<-<-.
    { rewrite indom_single_eq=><-. 
      rewrite /f /g; do ? case: classicT=> //; try lia. }
    all: move=> /[dup] ?.
    all: rewrite indom_Union=> -[]r[]/[dup]?.
    all: rewrite indom_interval /g=> ??.
    all: do ? (case: classicT=> //); try lia.
    all: try by case.
    all: rewrite /f; do ? case: classicT=> //=.
    all: case.
    { case: (@Get_in _ 0 N r x fsi1)=> //.
      rewrite indom_interval //. }
    case: (@Get_in _ 0 N r x fsi2)=> //.
    rewrite indom_interval //. }
  { rewrite /f; clear -iNj jNk kNi.
    case=> -[]l1 l2 x. rewrite ?indom_label_eq indom_single_eq=> -[][]<-<-<-.
    by do ? (case: classicT; try lia). }
  { rewrite /gi; clear -iNj jNk kNi.
    case=> -[]l1 l2 x ?. rewrite ?indom_label_eq indom_single_eq=> -[][]<-<-<-.
    by do ? (case: classicT; try lia). }
  { rewrite /fsi'=> ? _; clear -iNj jNk kNi.
    apply/disjoint_of_not_indom_both=> -[][]???.
    rewrite indom_union_eq=> -[].
    all: by rewrite ?indom_label_eq=> -[][]<- _ _ [][]; lia. }
  { rewrite /fsi'=> ? _; clear -iNj jNk kNi.
    apply/disjoint_of_not_indom_both=> -[][]???.
    rewrite indom_union_eq=> -[].
    all: by rewrite ?indom_label_eq=> -[][]<- _ _ [][]; lia. }
  { move=> ??; rewrite /fsi'; clear -iNj jNk kNi => ?.
    rewrite ?disjoint_union_eq_l ?disjoint_label; do ? split; left=> -[]; lia. }
  { move=> ?. 
    rewrite -Union_union_fset hbig_fset_union //.
    { rewrite -?Union_label ?hstar_fset_Lab /=. 
      do ? case: classicT=> *; subst=> //; xsimpl*.
      apply: himpl_trans; last exact/PostH; xsimpl.
      rewrite /r' /= ?eqbxx lbE1.
      by rewrite H'E. }
      do 2 rewrite disjoint_Union=> ??. 
      rewrite disjoint_label. left=> -[]. lia. } 
  { move=> > ? hvP; apply/opP=> // * /=; apply/hvP.
    all: rewrite indom_union_eq ?indom_label_eq; autos*. }
  move=> l Q ?; move: (IH l Q).
  rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
  rewrite union_empty_r => {}IH.
  have->: 
    (fun hr : D -> val =>
      Inv (l + 1) \*
      (\*_(d <- ⟨(j, 0), fsi1 l⟩ \u ⟨(k, 0), fsi2 l⟩) r' d) \*
      Q \(m, vd) H' l ((hr \o f) \o set2 l)) = 
    (fun v : D -> val => Inv (l + 1) \* (\*_(d <- ⟨(j, 0), fsi1 l⟩) R1' d) \* (\*_(d <- ⟨(j, 0), fsi2 l⟩) R2' d) \* Q \(m, vd) H' l v).
  { apply/fun_ext_1=> ?. 
    rewrite hbig_fset_union // .
    { rewrite -?Union_label ?hstar_fset_Lab /= /r' /= ?eqbxx lbE1.
      rewrite ?hstar_assoc; do 4 fequals.
      apply/opP=> // x ? /=; case: classicT=> // ?; try lia.
      { case: classicT=> // -[]; split=> //; lia. }
      case: classicT=> //.
      case: classicT=> // -[]. split=> //; lia. }
    do 2 rewrite disjoint_Union=> ??. 
    rewrite disjoint_single /= => -[]; lia. }
  rewrite hbig_fset_union //; first last.
  { do 2 rewrite disjoint_Union=> ??. 
    rewrite disjoint_single /= => -[]; lia. }
  rewrite -?Union_label ?hstar_fset_Lab /= /r /= ?eqbxx lbE1.
  (* case: classicT=> // ?; case: classicT=> // [[]|?]; first lia. *)
  rewrite hstar_assoc.
  rewrite ?hstar_fset_Lab /= in IH.
  erewrite wp_ht_eq; first (apply/IH; lia).
  case=> l' ?; rewrite ?indom_union_eq ?indom_label_eq=> -[][][]??; subst.
  { rewrite uni_in ?indom_label_eq //= /htrm_of.
    case: classicT=> //; autos*. }
  { have?: (i, 0) <> (j, 0) by case.
    rewrite uni_nin ?indom_label_eq /= /htrm_of; autos*.
    do ? (case: classicT=> //=; autos* ).
    { move=> [_]??[]; split=> //.
      rewrite indom_Union; setoid_rewrite indom_interval; do ? (eexists; eauto). }
    move=> ?? []; splits*; rewrite indom_Union; setoid_rewrite indom_interval; do ? (eexists; eauto). }
  have?: (i, 0) <> (k, 0) by case; lia.
  have?: (j, 0) <> (k, 0) by case; lia.
  rewrite uni_nin ?indom_label_eq /= /htrm_of; autos*.
  do ? (case: classicT=> //=; autos* ).
  move=> [_]??[]; split=> //.
  rewrite indom_Union; setoid_rewrite indom_interval; do ? (eexists; eauto).
Qed.

Lemma xfor_lemma_gen2_bigstr `{ID : Inhab D}
  Inv 
  (R1 R1' R2 R2' : Dom -> hhprop)
  s fsi1 fsi2 vr H H'
  (N: Z) (C1 C2 : Dom -> trm) (C : trm)
  (i j k : Z)
  Pre Post: 
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1 d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2 d) \* 
        H l }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1' d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2' d) \* 
        H' l v }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall j : int, hlocal (H j) ⟨(i,0%Z), single s tt⟩) ->
  (forall (j : int) (v : D -> val), hlocal (H' j v) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R1 i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R1' i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R2 i) ⟨(k,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R2' i) ⟨(k,0%Z), single i tt⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    (forall i, indom (fsi2 m) i -> hv[`k](i) = hv'[`k](i)) ->
    H' m hv = H' m hv') ->
  (i <> j)%Z ->
  (j <> k)%Z ->
  (k <> i)%Z ->
  0 <= N ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R1 d) \*
    (\*_(d <- Union `[0,N] fsi2) R2 d) \*
    \*_(i <- `[0,N]) H i) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R1' d) \* 
    (\*_(d <- Union `[0,N] fsi2) R2' d) \* 
    (\*_(i <- `[0,N]) H' i hv) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For 0 N (trm_fun vr C)};
      {j| ld in Union `[0,N] fsi1 => C1 ld};
      {k| ld in Union `[0,N] fsi2 => C2 ld}
    }]
  {{ v, Post v }}. 
Proof.
  move=> IH *; eapply xfor_lemma2_hbig_op with 
  (m := fun _ _ => 0)
  (Inv := Inv)
  (vd := fun=> False)
  (R1 := R1) (R2 := R2) (R2' := R2') (R1' := R1'); try eassumption; autos*=> //.
  all: rewrite -hmerge_hstar //.
  move=> ? Q ?.
  xframe2 Q. exact/IH.
Qed.

Lemma xfor_lemma_gen_bigstr `{ID : Inhab D}
  Inv 
  (R R' : Dom -> hhprop)
  s fsi1 vr H H'
  (N: Z) (C1 : Dom -> trm) (C : trm)
  (i j : Z)
  Pre Post: 
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R d) \* 
        H l }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R' d) \* 
        H' l v }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall j : int, hlocal (H j) ⟨(i,0%Z), single s tt⟩) ->
  (forall (j : int) (v : D -> val), hlocal (H' j v) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R' i) ⟨(j,0%Z), single i tt⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    H' m hv = H' m hv') ->
  (i <> j)%Z ->
  0 <= N ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R d) \*
    \*_(i <- `[0,N]) H i) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R' d) \* 
    (\*_(i <- `[0,N]) H' i hv) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For 0 N (trm_fun vr C)};
      {j| ld in Union `[0,N] fsi1 => C1 ld}
    }]
  {{ v, Post v }}. 
Proof.
  move=> IH *; eapply xfor_lemma with 
  (m := fun _ _ => 0)
  (Inv := Inv)
  (vd := fun=> False)
  (R := R) (R' := R'); try eassumption; autos*=> //.
  all: rewrite -hmerge_hstar //.
  move=> ? Q ?.
  xframe2 Q. exact/IH.
Qed.

Lemma xfor_lemma_gen2_array `{ID : Inhab D}
  Inv 
  (R1 R1' R2 R2' : Dom -> hhprop)
  s fsi1 fsi2 vr (arrl : loc) (arr1 : list int) arr2 idx
  (N M : Z) (C1 C2 : Dom -> trm) (C : trm)
  (i j k : Z)
  Pre Post: 
  (forall v, length (arr2 v) = M :> int) ->
  length arr1 = M :> int ->
  length idx = N :> int ->
  NoDup idx ->
  (forall (l : int), 
    (0 <= l < N) -> 0 <= idx[l] < M) ->
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1 d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2 d) \* 
        (arrl + 1 + abs idx[l])%nat ~⟨(i,0)%Z, s⟩~> arr1[idx[l] ] }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1' d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2' d) \* 
        (arrl + 1 + abs idx[l])%nat ~⟨(i,0)%Z, s⟩~> (arr2 v)[idx[l] ] }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R1 i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R1' i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R2 i) ⟨(k,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R2' i) ⟨(k,0%Z), single i tt⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    (forall i, indom (fsi2 m) i -> hv[`k](i) = hv'[`k](i)) ->
    (arr2 hv)[idx[m] ] = (arr2 hv')[idx[m] ]) ->
  (forall (hv : D -> val) m,
    0 <= m < M -> ~ In m idx -> arr1[m] = (arr2 hv)[m]) ->
  (i <> j)%Z ->
  (j <> k)%Z ->
  (k <> i)%Z ->
  0 <= N ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R1 d) \*
    (\*_(d <- Union `[0,N] fsi2) R2 d) \*
    harray_int arr1 arrl (Lab (i,0) s)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R1' d) \* 
    (\*_(d <- Union `[0,N] fsi2) R2' d) \* 
    harray_int (arr2 hv) arrl (Lab (i,0) s) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For 0 N (trm_fun vr C)};
      {j| ld in Union `[0,N] fsi1 => C1 ld};
      {k| ld in Union `[0,N] fsi2 => C2 ld}
    }]
  {{ v, Post v }}. 
Proof.
  move=>  AL1 AL2 ALidx Hnodup Hidx IH ????? hvE Hpre ????????? PreH PostH.
  have AL : forall hv, Datatypes.length arr1 = Datatypes.length (arr2 hv).
  { move=> v; move: (AL1 v). lia. }
  have Hidx' : forall x : int, In x idx -> 0 <= x < M.
  { intros. eapply In_nth with (d:=0) in H. destruct H as (n & Hn & <-). 
    replace n with (abs n)%nat by math. apply Hidx. math. }
  apply/ntriple_conseq; last exact/PostH; eauto.
  rewrite /harray_int/harray/hheader ?length_map ?length_List_length.
  apply/(ntriple_conseq); [|exact: himpl_trans|move=> ?]; first last.
  { rewrite /harray_int/harray/hheader ?length_map ?length_List_length -AL.
    move=> ?; apply:applys_eq_init; reflexivity. }
  xframe2 (arrl ~⟨(i, 0%Z), s⟩~> val_header (length arr1)).
  xframe2 \[(arrl, (⟨(i, 0), s⟩)%arr) <> null (⟨(i, 0), s⟩)%arr].
  rewrite ?hcellsE_int AL2.
  rewrite -> hbig_fset_part with (fs:=`[0, M]) (P:=idx).
  set (Inv' := hbig_fset _ (_ ∖ _) _).
  rewrite intr_list // (fset_of_list_nodup 0) // ALidx hbig_fset_Union.
  2:{ introv Ha Hb Hc. apply disjoint_single_single. intros Hd. rewrite ! indom_interval in Hb, Hc. apply Ha. enough (abs i0 = abs j0) by lia.
    move: Hd. erewrite -> NoDup_nth in Hnodup. apply Hnodup; math. }
  eapply xfor_lemma_gen2_bigstr with 
  (Inv := fun i => Inv i \* Inv')
  (H := fun l => (arrl + 1 + abs idx[l])%nat ~⟨(i, 0%Z), s⟩~> arr1[idx[l] ])
  (H' := fun l v => (arrl + 1 + abs idx[l])%nat ~⟨(i, 0%Z), s⟩~> (arr2 v)[idx[l] ])
  (R1 := R1) (R2 := R2) (R2' := R2') (R1' := R1'); try eassumption; autos*=> //.
  { move=> l Hl. xframe2 Inv'. rewrite wp_equiv. eapply htriple_conseq. 1: apply wp_equiv, IH=> //. all: xsimpl*. 
    (* xnsimpl will make over simplification *) }
  { rewrite /Inv'. xlocal. autos*. }
  { xlocal. }
  { xlocal. }
  { move=> ???? hvE1 hvE2; erewrite hvE; eauto. }
  { xsimpl*=> ?; apply:applys_eq_init. f_equal. extens=> ?. 
   by rewrite hstar_fset_label_single. }
  move=> ?. rewrite /Inv' hcellsE_int AL1 !fun_eta_1. xsimpl*. 
  rewrite -> hbig_fset_part with (fs:=`[0, M]) (P:=idx).
  rewrite intr_list // (fset_of_list_nodup 0) // ALidx hbig_fset_Union.
  2:{ introv Ha Hb Hc. apply disjoint_single_single. intros Hd. rewrite ! indom_interval in Hb, Hc. apply Ha. enough (abs i0 = abs j0) by lia.
    move: Hd. erewrite -> NoDup_nth in Hnodup. apply Hnodup; math. }
  erewrite hbig_fset_eq with (fs:=`[0, N]). 1: xsimpl*. 2: move=> * /=; by rewrite hbig_fset_label_single'.
  erewrite hbig_fset_eq. 1: xsimpl*. 
  move=> d Hnotin /=. rewrite filter_indom indom_interval /LibSummation.mem /= in Hnotin. do 2 f_equal. now apply Hpre.
Qed.

(* TODO it might be easier to change some_eq to be on some type A, and use the toval trick again 
    otherwise its application would be complicated (e.g., for float) *)
Lemma xfor_lemma_gen_array `{ID : Inhab D} (some_eq : Relation_Definitions.relation val) `{Heqv : @RelationClasses.Equivalence val some_eq}
  Inv 
  (R R' : Dom -> hhprop)
  s fsi1 vr (arrl : loc) (def : val) (arr1 : list val) (arr2 : (D -> val) -> list val) (idx : list int)
  (N M : Z) (C1 : Dom -> trm) (C : trm)
  (i j : Z)
  Pre Post: 
  (forall v, length (arr2 v) = M :> int) ->
  length arr1 = M :> int ->
  length idx = N :> int ->
  NoDup idx ->
  (forall (l : int), 
    (0 <= l < N) -> 0 <= idx[l] < M) ->
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> nth (abs (idx[l])) arr1 def }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ v, \exists vv : val, 
        \[some_eq vv (nth (abs (idx[l])) (arr2 v) def)] \*
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R' d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> vv }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : Dom, hlocal (R' i) ⟨(j,0%Z), single i tt⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    some_eq (nth (abs (idx[m])) (arr2 hv) def) (nth (abs (idx[m])) (arr2 hv') def)) ->
  (forall (hv : D -> val) m,
    0 <= m < M -> ~ In m idx -> some_eq (nth (abs m) arr1 def) (nth (abs m) (arr2 hv) def)) ->
  (i <> j)%Z ->
  0 <= N <= M ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R d) \*
    harray arr1 arrl (Lab (i,0) s)) ->
  (forall hv (vl : int -> val),
    \[forall i : int, 0 <= i < M -> some_eq (vl i) (nth (abs i) (arr2 hv) def)] \*
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R' d) \* 
    harray (projT1 (list_of_fun' vl M)) arrl (Lab (i,0) s) ==>
    Post hv) ->
  {{ Pre }}
    [{
      {i| _  in single s tt => For 0 N (trm_fun vr C)};
      {j| ld in Union `[0,N] fsi1 => C1 ld}
    }]
  {{ v, Post v }}. 
Proof.
  move=> AL1 AL2 ALidx Hnodup Hidx IH ??? hvE Hre ???????? PreH PostH.
  have AL : forall hv, Datatypes.length arr1 = Datatypes.length (arr2 hv).
  { move=> v; move: (AL1 v). lia. }
  have Hidx' : forall x : int, In x idx -> 0 <= x < M.
  { intros. eapply In_nth with (d:=0) in H. destruct H as (n & Hn & <-). 
    replace n with (abs n)%nat by math. apply Hidx. math. }
  apply/ntriple_conseq; [ | apply PreH | apply qimpl_refl ].
  rewrite /harray/hheader ?length_map ?length_List_length.
  (*
  rewrite /harray/hheader ?length_map ?length_List_length -AL.
    move=> ?; apply:applys_eq_init; reflexivity.
  apply/(ntriple_conseq); [|eapply himpl_trans|apply qimpl_refl].
  { rewrite /harray/hheader ?length_map ?length_List_length -AL.
    move=> ?; apply:applys_eq_init; reflexivity. }
  *)
  (* xframe2 (arrl ~⟨(i, 0%Z), s⟩~> val_header (length arr1)).
  xframe2 \[(arrl, (⟨(i, 0), s⟩)%arr) <> null (⟨(i, 0), s⟩)%arr]. *)
  rewrite ?(hcellsE _ def) AL2.
  rewrite -> hbig_fset_part with (fs:=`[0, M]) (P:=idx).
  set (Inv'' := hbig_fset _ (_ ∖ _) _).
  pose (Inv' := \[(arrl, (⟨(i, 0), s⟩)%arr) <> null (⟨(i, 0), s⟩)%arr] \*
    (arrl ~⟨(i, 0%Z), s⟩~> val_header (length arr1)) \* Inv'').
  rewrite intr_list // (fset_of_list_nodup 0) // ALidx hbig_fset_Union.
  2:{ introv Ha Hb Hc. apply disjoint_single_single. intros Hd. rewrite ! indom_interval in Hb, Hc. apply Ha. enough (abs i0 = abs j0) by lia.
    move: Hd. erewrite -> NoDup_nth in Hnodup. apply Hnodup; math. }
  erewrite hbig_fset_eq with (fs:=`[0, N]). 2: intros; rewrite hbig_fset_label_single'; reflexivity.
  eapply xfor_lemma_gen_bigstr with 
  (Inv := fun i => Inv i \* Inv')
  (H := fun l => (arrl + 1 + abs (idx[l]))%nat ~⟨(i, 0%Z), s⟩~> nth (abs (idx[l])) arr1 def)
  (H' := fun l v => \exists vv : val, 
    \[some_eq vv (nth (abs (idx[l])) (arr2 v) def)] \*
    (arrl + 1 + abs (idx[l]))%nat ~⟨(i, 0%Z), s⟩~> vv)
  (R := R) (R' := R'); try eassumption; autos*=> //.
  { move=> l Hl. xframe2 Inv'. rewrite wp_equiv. eapply htriple_conseq. 1: apply wp_equiv, IH=> //. all: xsimpl*. 
    (* xnsimpl will make over simplification *) }
  { rewrite /Inv'. xlocal. autos*. apply hlocal_hstar_fset. xlocal. }
  { xlocal. }
  { xlocal. }
  { move=> ???? hvE1. apply himpl_antisym; xsimpl=>?; rewrite hvE; eauto. intros; symmetry; auto. }
  { rewrite/Inv' /Inv''; xsimpl*. }
  (* TODO the following part is very bad; need improvement *)
  move=> hv. rewrite hstar_fset_hexists. xsimpl*=> vl.
  rewrite hstar_fset_pure_hstar. xsimpl*=> Hvl. setoid_rewrite indom_interval in Hvl.
  pose (vl' := fun i : int => If In i idx then vl (LibListExt.index i idx) else (nth (abs i) arr1 def)).
  eapply himpl_trans. 2: apply (PostH hv vl'). 
  assert (forall i0 : int, 0 <= i0 < M -> some_eq (vl' i0) (nth (abs i0) (arr2 hv) def)) as Htmp.
  { intros i0 Hi0. rewrite /vl'. case_if.
    { rewrite Hvl. 2: split; [ apply indexG0 | rewrite -index_mem in C0; math ].
      rewrite nth_index //. reflexivity. }
    { apply Hre; try math; auto. } }
  destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
  xsimpl*. rewrite /harray/hheader/Inv'/Inv'' (hcellsE _ def) ?length_List_length. xsimpl*=>_. 
  replace (Z.of_nat (length l1)) with M by math. 
  replace (length l1) with (length arr1) by math. xsimpl*.
  rewrite -> hbig_fset_part with (fs:=`[0, M]) (P:=idx).
  rewrite intr_list // (fset_of_list_nodup 0) // ALidx hbig_fset_Union.
  2:{ introv Ha Hb Hc. apply disjoint_single_single. intros Hd. rewrite ! indom_interval in Hb, Hc. apply Ha. enough (abs i0 = abs j0) by lia.
    move: Hd. erewrite -> NoDup_nth in Hnodup. apply Hnodup; math. }
  erewrite hbig_fset_eq with (fs:=`[0, N]). 1: xsimpl*. 
  2: move=> d Hd /=; rewrite indom_interval in Hd; specialize (Hidx d Hd); rewrite hbig_fset_label_single' Hl1 /vl' ?index_nodup //; try math.
  2: assert (In idx[d] idx) by (apply nth_In; math); case_if; eqsolve.
  erewrite hbig_fset_eq. 1: xsimpl*. 
  move=> d Hnotin /=. rewrite filter_indom indom_interval /LibSummation.mem /= in Hnotin. f_equal. 
  rewrite Hl1 /vl'; try math. case_if; eqsolve.
Qed.


Lemma xfor_lemma_gen_array_fun_aux `{ID : Inhab D}
  Inv 
  (R R' : Dom -> hhprop)
  s fsi1 vr (arrl : loc) (f : int -> int) (g : _ -> _ -> int) (idx : list int)
  (N M:int) (C1 : Dom -> trm) (C : trm)
  (i j : int)
  Pre Post: 
  length idx = N :> int ->
  NoDup idx ->
  (forall (l : int), 
    (0 <= l < N) -> 0 <= idx[l] < M) ->
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> f (idx[l]) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R' d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> g v (idx[l]) }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R' i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    g hv (idx[m]) = g hv' (idx[m])) ->
  (forall (hv : D -> val) m,
    0 <= m < M -> ~ In m idx -> f m = g hv m) ->
  (i <> j)%Z ->
  0 <= N <= M ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R d) \*
    harray_fun_int f arrl M (Lab (i,0) s)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R' d) \* 
    harray_fun_int (g hv) arrl M (Lab (i,0) s) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For 0 N (trm_fun vr C)};
      {j| ld in Union `[0,N] fsi1 => C1 ld}
    }]
  {{ v, Post v }}. 
Proof.
  move=>lenidx nodup_idx idx_bounded IH *.
  eapply xfor_lemma_gen_array with (R := R) (R' := R') (arr1 := LibList.map val_int (lof f M)) (arr2 := fun hv => LibList.map val_int (lof (g hv) M)) (arrl:=arrl) (def:=val_int 0) (some_eq:=eq); try eassumption.
  1: constructor; hnf; congruence. 
  { move=> ?; rewrite map_conversion map_length length_lof; math. }
  { rewrite map_conversion map_length length_lof; math. }
  { move=> l P; rewrite map_conversion map_nth nth_lof' //; try math; auto.
    apply/ntriple_conseq; [apply (IH l P) | |move=> v; rewrite map_conversion map_nth nth_lof'//; try math; auto]; xsimpl*. }
  all: try (move=> *; rewrite ?map_conversion ?map_nth ?nth_lof' //; f_equal; try math; auto).
  xsimpl=>HH. eapply himpl_trans. 2: eauto. xsimpl*.
  rewrite /harray_fun_int/harray_int map_conversion.
  rewrite -(lof_indices) !(lof_indices') in HH |- *.
  eapply eq_ind_r with (y:=map _ _); [ xsimpl* | ].
  apply map_ext_in=> a /In_lof_id Hin /=. rewrite HH ?(nth_map_lt 0) ?nth_lof' ?length_lof' //; try math.
Qed.


Lemma xfor_lemma_gen_array_fun `{ID : Inhab D}
  Inv 
  (R R' : Dom -> hhprop)
  s fsi1 vr (arrl : loc) (f : int -> int) (g : _ -> _ -> int) (idx : list int)
  (N M : Z) (C1 : Dom -> trm) (C C' : trm)
  (i j : Z)
  Pre Post: 
  length idx = N :> int ->
  NoDup idx ->
  (forall (l : int), 
    (0 <= l < N) -> 0 <= idx[l] < M) ->
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> f (idx[l]) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R' d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> g v (idx[l]) }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R' i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    g hv (idx[m]) = g hv' (idx[m])) ->
  (forall (hv : D -> val) m,
    0 <= m < M -> ~ In m idx -> f m = g hv m) ->
  (i <> j)%Z ->
  0 <= N <= M ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R d) \*
    harray_fun_int f arrl M (Lab (i,0) s)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R' d) \* 
    harray_fun_int (g hv) arrl M (Lab (i,0) s) ==>
    wp ⟨(i,0),single s tt⟩ (fun=> C') (fun hr' => Post (lab_fun_upd hr' hv (i,0)))) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => trm_seq (For 0 N (trm_fun vr C)) C'};
      {j| ld in Union `[0,N] fsi1 => C1 ld}
    }]
  {{ v, Post v }}.
Proof.
  intros.
  xfocus (j,0); rewrite ?eqbxx.
  have E: (lab_eqb (i, 0) (j,0) = false).
  { by apply/bool_ext; split=> //; rewrite lab_eqbE=> -[]. }
  rewrite E/= -xnwp1_lemma /= wp_equiv.
  apply/htriple_conseq; [|eauto|]; first last.
  { move=> ?. apply/wp_seq. }
  rewrite (xnwp1_lemma (FH (single s tt) (fun=> For 0 N <{ fun_ {vr} => {C} }>)) ((i,0))).
  rewrite -wp_equiv.
  apply/(@xunfocus_lemma _ (fun hr => WP [ _ in ⟨(i, 0), single s tt⟩  => C' ]
  { hr'0, Post ((hr \u_ ⟨(j, 0), Union (interval 0 N) fsi1⟩) hr'0) }))=> /=; autos*.
  { by rewrite E. }
  move=> ??; fequals; apply/fun_ext_1=> ?. fequals.
  extens=> -[]??; rewrite /uni; case: classicT=> //.
  xfocus (i,0); rewrite ?eqbxx lab_eqb_sym E /=.
  apply/xunfocus_lemma; autos*=> /=.
  { by rewrite lab_eqb_sym E. }
  { move=> ??. remember ((_ \u_ _) _); reflexivity. }
  simpl.
  apply/xfor_lemma_gen_array_fun_aux; try eassumption; eauto.
  move=> hv. apply: himpl_trans; [|apply/wp_hv].
  move: (H17 hv); rewrite wp_equiv=> ?.
  xapp=> hv'. rewrite -/(lab_fun_upd _ _ _).
  xsimpl (lab_fun_upd hv' hv (i, 0))=> ?.
  apply: applys_eq_init; fequals; apply/fun_ext_1=> /=.
  case=> l x.
  rewrite /uni ?indom_label_eq; case: classicT.
  { by case=> <- /=; rewrite lab_eqb_sym E. }
  case: classicT=> //.
  case=> <- /=; rewrite eqbxx //.
Qed.

Lemma xfor_lemma_gen_array_fun_aux2 `{ID : Inhab D}
  Inv 
  (R1 R1' R2 R2' : Dom -> hhprop)
  s fsi1 fsi2 vr (arrl : loc) (f : int -> int) (g : _ -> _ -> int) idx
  (N M: Z) (C1 C2 : Dom -> trm) (C : trm)
  (i j k : Z)
  Pre Post: 
  length idx = N :> int ->
  NoDup idx ->
  (forall (l : int), 
    (0 <= l < N) -> 0 <= idx[l] < M) ->
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1 d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2 d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> f (idx[l]) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1' d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2' d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> g v (idx[l]) }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R1 i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R1' i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R2 i) ⟨(k,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R2' i) ⟨(k,0%Z), (single i tt)⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    (forall i, indom (fsi2 m) i -> hv[`k](i) = hv'[`k](i)) ->
    g hv (idx[m]) = g hv' (idx[m])) ->
  (forall (hv : D -> val) m,
    0 <= m < M -> ~ In m idx -> f m = g hv m) ->
  (i <> j)%Z ->
  (j <> k)%Z ->
  (k <> i)%Z ->
  0 <= N <= M ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R1 d) \*
    (\*_(d <- Union `[0,N] fsi2) R2 d) \*
    harray_fun_int f arrl M (Lab (i,0) s)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R1' d) \*
    (\*_(d <- Union `[0,N] fsi2) R2' d) \* 
    harray_fun_int (g hv) arrl M (Lab (i,0) s) ==>
     Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => (For 0 N (trm_fun vr C))};
      {j| ld in Union `[0,N] fsi1 => C1 ld};
      {k| ld in Union `[0,N] fsi2 => C2 ld}
    }]
  {{ v, Post v }}.
Proof.
  move=>??? IH *.
  eapply xfor_lemma_gen2_array with (R1 := R1) (R1' := R1') (R2 := R2) (R2' := R2') (arr1 := lof f M) (arr2 := fun hv => lof (g hv) M) (arrl:=arrl); try eassumption.
  { move=> ?; rewrite length_lof; math. }
  { apply length_lof; math. }
  { move=> l P; rewrite nth_lof' //; try math; auto.
    apply/ntriple_conseq; [ | |move=> v; rewrite nth_lof' //; try math; auto]; try exact:himpl_refl.
    rewrite -/(ntriple _ _ _).  auto. }
  all: move=> *; rewrite ?nth_lof' //; autos*.
Qed.

Lemma xfor_lemma_gen_array_fun2 `{ID : Inhab D}
  Inv 
  (R1 R1' R2 R2' : Dom -> hhprop)
  s fsi1 fsi2 vr (arrl : loc) (f : int -> int) (g : _ -> _ -> int) idx
  (N M: Z) (C1 C2 : Dom -> trm) (C C' : trm)
  (i j k : Z)
  Pre Post: 
  length idx = N :> int ->
  NoDup idx ->
  (forall (l : int), 
    (0 <= l < N) -> 0 <= idx[l] < M) ->
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1 d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2 d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> f (idx[l]) }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1' d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2' d) \* 
        (arrl + 1 + abs (idx[l]))%nat ~⟨(i,0)%Z, s⟩~> g v (idx[l]) }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R1 i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R1' i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R2 i) ⟨(k,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R2' i) ⟨(k,0%Z), (single i tt)⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    (forall i, indom (fsi2 m) i -> hv[`k](i) = hv'[`k](i)) ->
    g hv (idx[m]) = g hv' (idx[m])) ->
  (forall (hv : D -> val) m,
    0 <= m < M -> ~ In m idx -> f m = g hv m) ->
  (i <> j)%Z ->
  (j <> k)%Z ->
  (k <> i)%Z ->
  0 <= N <= M ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R1 d) \*
    (\*_(d <- Union `[0,N] fsi2) R2 d) \*
    harray_fun_int f arrl M (Lab (i,0) s)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R1' d) \*
    (\*_(d <- Union `[0,N] fsi2) R2' d) \* 
    harray_fun_int (g hv) arrl M (Lab (i,0) s) ==>
    wp ⟨(i,0),single s tt⟩ (fun=> C') (fun hr' => Post (lab_fun_upd hr' hv (i,0)))) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => trm_seq (For 0 N (trm_fun vr C)) C'};
      {j| ld in Union `[0,N] fsi1 => C1 ld};
      {k| ld in Union `[0,N] fsi2 => C2 ld}
    }]
  {{ v, Post v }}.
Proof.
  move=> ?????????????????????? PostH.
  eapply ntriple_sequ2_gen with (Q' := fun hv=> Inv N \*
    (\*_(d <- \U_(i <- `[0, N]) fsi1 i) R1' d) \*
    (\*_(d <- \U_(i <- `[0, N]) fsi2 i) R2' d) \*
    harray_fun_int (g hv) arrl M (Lab (i,0) s)); autos*=> /=.
  { apply/xfor_lemma_gen_array_fun_aux2; try eassumption; xsimpl*. }
  { move=> v; rewrite -wp_equiv; apply: himpl_trans_r.
    apply/wp_hv; apply: wp_conseq Hwp=> hr ? Qh.
    setoid_rewrite wp_equiv in PostH; xapp=> hr.
    xsimpl (lab_fun_upd hr v (i, 0))=> ?; apply:applys_eq_init; f_equal; extens=> -[??].
    rewrite /uni; case: classicT.
    { rewrite union_empty_r indom_union_eq ?indom_label_eq.
      case: ssrbool.ifP=> //. 
      rewrite /is_true bool_eq_true_eq lab_eqbE /==>->[][][]; eqsolve. } 
    rewrite indom_label_eq indom_single_eq. 
    by case: classicT=> // -[]<-<-/= /[! eqbxx]. }
  rewrite Bool.orb_false_r.
  case E: (lab_eqb _ _); move: E=> /=.
  { move<-. rewrite lab_eqbE. eqsolve. }
  rewrite lab_eqbE. eqsolve.
Qed.

Lemma xfor_lemma_gen_array_fun_normal `{ID : Inhab D}
  Inv 
  (R R' : Dom -> hhprop)
  s fsi1 vr (arrl : loc) (f : int -> int) (g : _ -> _ -> int)
  (N: Z) (C1 : Dom -> trm) (C C' : trm)
  (i j : Z)
  Pre Post: 
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R d) \* 
        (arrl + 1 + abs l)%nat ~⟨(i,0)%Z, s⟩~> f l }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R' d) \* 
        (arrl + 1 + abs l)%nat ~⟨(i,0)%Z, s⟩~> g v l }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R' i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    g hv m = g hv' m) ->
  (i <> j)%Z ->
  0 <= N ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R d) \*
    harray_fun_int f arrl N (Lab (i,0) s)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R' d) \* 
    harray_fun_int (g hv) arrl N (Lab (i,0) s) ==>
    wp ⟨(i,0),single s tt⟩ (fun=> C') (fun hr' => Post (lab_fun_upd hr' hv (i,0)))) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => trm_seq (For 0 N (trm_fun vr C)) C'};
      {j| ld in Union `[0,N] fsi1 => C1 ld}
    }]
  {{ v, Post v }}.
Proof.
  intros.
  have El : List.length (lof (@id int) N) = abs N :> nat.
  { match goal with |- ?a = _ => enough (a = N :> int) by math end. apply length_lof; math. }
  eapply xfor_lemma_gen_array_fun with (idx:=lof (@id int) N) (f:=f) (g:=g) (R:=R) (R':=R'); 
    try eassumption; try math; eauto.
  { apply NoDup_nth with (d:=0). intros. rewrite -> ! El in *.
    replace i0 with (abs i0)%nat in * by math.
    replace j0 with (abs j0)%nat in * by math. rewrite -> ! nth_lof in *; math. }
  { intros. rewrite nth_lof; math. }
  { intros. rewrite nth_lof; try math. auto. }
  { intros. rewrite nth_lof; try math. auto. }
  { intros hv m HH HH2. false HH2. replace m with ((lof id N)[m]) by (rewrite nth_lof; math).
    apply nth_In. math. }
Qed.

Lemma xfor_lemma_gen_array_fun_normal2 `{ID : Inhab D}
  Inv 
  (R1 R1' R2 R2' : Dom -> hhprop)
  s fsi1 fsi2 vr (arrl : loc) (f : int -> int) (g : _ -> _ -> int)
  (N: Z) (C1 C2 : Dom -> trm) (C C' : trm)
  (i j k : Z)
  Pre Post: 
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1 d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2 d) \* 
        (arrl + 1 + abs l)%nat ~⟨(i,0)%Z, s⟩~> f l }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1' d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2' d) \* 
        (arrl + 1 + abs l)%nat ~⟨(i,0)%Z, s⟩~> g v l }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : Dom, hlocal (R1 i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R1' i) ⟨(j,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R2 i) ⟨(k,0%Z), (single i tt)⟩) ->
  (forall i : Dom, hlocal (R2' i) ⟨(k,0%Z), (single i tt)⟩) ->
  (forall (hv hv' : D -> val) m,
    0 <= m < N ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    (forall i, indom (fsi2 m) i -> hv[`k](i) = hv'[`k](i)) ->
    g hv m = g hv' m) ->
  (i <> j)%Z ->
  (j <> k)%Z ->
  (k <> i)%Z ->
  0 <= N ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union `[0,N] fsi1) R1 d) \*
    (\*_(d <- Union `[0,N] fsi2) R2 d) \*
    harray_fun_int f arrl N (Lab (i,0) s)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R1' d) \* 
    (\*_(d <- Union `[0,N] fsi2) R2' d) \* 
    harray_fun_int (g hv) arrl N (Lab (i,0) s) ==>
    wp ⟨(i,0),single s tt⟩ (fun=> C') (fun hr' => Post (lab_fun_upd hr' hv (i,0)))) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => trm_seq (For 0 N (trm_fun vr C)) C'};
      {j| ld in Union `[0,N] fsi1 => C1 ld};
      {k| ld in Union `[0,N] fsi2 => C2 ld}
    }]
  {{ v, Post v }}.
Proof.
  intros.
  have El : List.length (lof (@id int) N) = abs N :> nat.
  { match goal with |- ?a = _ => enough (a = N :> int) by math end. apply length_lof; math. }
  eapply xfor_lemma_gen_array_fun2 with (idx:=lof (@id int) N) (f:=f) (g:=g) (R1:=R1) (R2:=R2) (R1':=R1') (R2':=R2'); 
    try eassumption; try math; eauto.
  { apply NoDup_nth with (d:=0). intros. rewrite -> ! El in *.
    replace i0 with (abs i0)%nat in * by math.
    replace j0 with (abs j0)%nat in * by math. rewrite -> ! nth_lof in *; math. }
  { intros. rewrite nth_lof; math. }
  { intros. rewrite nth_lof; try math. auto. }
  { intros. rewrite nth_lof; try math. auto. }
  { intros hv m HH HH2. false HH2. replace m with ((lof id N)[m]) by (rewrite nth_lof; math).
    apply nth_In. math. }
Qed.

End WithLoops.

Tactic Notation "xfor_sum_cong_solve" uconstr(op) :=
  let hvE := fresh "hvE" in
  let someindom := fresh "someindom" in
  intros ???? hvE; (try case_if=> //; [ ]); rewrite ?/op; indomE;
  match goal with 
  | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ?; indomE; intros someindom; extens; intros 
  | _ => idtac
  end; try (setoid_rewrite hvE; [eauto|autorewrite with indomE; try math; 
    (first [ apply someindom | idtac ])]).

Ltac xfor_sum_core is_int_mode Inv R R' op s :=
  match is_int_mode with
  | true => eapply (@xfor_big_op_lemma_int _ _ Inv R R' op s)
  | false => eapply (@xfor_big_op_lemma _ _ _ _ Inv R R' val_float float_unit (float_unit, float_unit) (fun a (b : binary64 * binary64) => @BFMA _ Tdouble b.1 b.2 a) 
    (fun (b : binary64 * binary64) => @finite Tdouble b.1 /\ @finite Tdouble b.2) op s)
  end;
  [ let L := fresh in 
    intros ?? L; rewrite ?/Inv ?/R ?/R';
    xnsimpl
  | disjointE
  | xfor_sum_cong_solve op
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
  ]=> //; autos*.

Tactic Notation "xfor_sum" constr(Inv) constr(R) uconstr(R') uconstr(op) constr(s) :=
  match goal with
  | |- context[hsingle s _ (val_int _)] => xfor_sum_core true Inv R R' op s
  | |- context[hsingle s _ (val_float _)] => xfor_sum_core false Inv R R' op s
  end.

Ltac xwhile1 Z N b Inv := 
  let N := constr:(N) in
  let Z := constr:(Z) in 
  let Inv' := constr:(Inv) in
  xseq_xlet_if_needed; xstruct_if_needed;
  eapply (wp_while_unary Inv b (Z := Z) (N := N)); autos*.

Tactic Notation "xwhile_sum" 
    constr(Inv) 
    constr(R1) constr(R2) 
    uconstr(R1') uconstr(R2') 
    constr(op) constr(s) :=
  eapply (@xwhile_big_op_lemma2 _ _
    Inv R1 R2 R1' R2' op s)=> //;
  [
  |
  |
  | intro; rewrite ?/Inv; xsimpl*
  | disjointE
  | disjointE 
  | let hvE1 := fresh "hvE1" in
    let hvE2 := fresh "hvE2" in
    let someindom := fresh "someindom" in
    intros ??? hvE1 hvE2; rewrite ?/op;
    match goal with 
    | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ? someindom; extens; intros 
    | _ => idtac
    end; try setoid_rewrite hvE1; try setoid_rewrite hvE2 
    (**; [eauto|autorewrite with indomE; try math; 
    (first [ apply someindom | idtac ])]*)
  | try lia
  |
  |
  ].

Tactic Notation "xset_Inv_core1" ident(Inv) constr(h) constr(H) := 
  (* idtac h; *)
  let Inv1 := fresh "Inv" in 
  set (Inv1 := h);
  match constr:(h) with 
  | context[H] => idtac
  | _ =>
    let Inv_tmp := fresh "Inv" in 
    (* idtac "AA"; *)
    set (Inv_tmp := fun d => Inv1 \* Inv d);
    (* idtac "BB"; *)
    unfold Inv1, Inv in Inv_tmp;
    clear Inv; rename Inv_tmp into Inv
  end.

Ltac xset_Inv_core Inv i H := 
  repeat match goal with 
  | |- context[@hsingle _ ?p (Lab (i%Z, 0) ?x) ?v] =>
    let t := type of x in
    (try set (Inv := fun (k: int) => \[] : (hhprop (labeled t))));
    xset_Inv_core1 Inv ((@hsingle _ p (Lab (i%Z, 0) x) v)) H
  | |- context[@harray_int _ ?L ?p (Lab (i%Z, 0) ?x)] =>
    let t := type of x in
    (* idtac "AA";  *)
    (try set (Inv := fun (k: int) => \[] : (hhprop (labeled t))));
    (* idtac "BB";  *)
    xset_Inv_core1 Inv ((@harray_int _ L p (Lab (i%Z, 0) x))) H
  | |- context[@harray_float _ ?L ?p (Lab (i%Z, 0) ?x)] =>
    let t := type of x in
    (try set (Inv := fun (k: int) => \[] : (hhprop (labeled t))));
    xset_Inv_core1 Inv ((@harray_float _ L p (Lab (i%Z, 0) x))) H
  end.

Tactic Notation "xset_clean" ident(ia) ident(ib) ident(ic) := 
  repeat multimatch goal with 
  | H := ?b |- _ => 
    (* idtac H; *)
    tryif constr_eq_strict H ia then fail else
    tryif constr_eq_strict H ib then fail else
    tryif constr_eq_strict H ic then fail else
    unfold H; clear H
  end.

Tactic Notation "xset_Inv" ident(Inv) constr(i) uconstr(H) := 
  xset_Inv_core Inv i H; xset_clean Inv Inv Inv.

Tactic Notation "xset_Inv" ident(Inv) constr(i) := 
  xset_Inv_core Inv i (239); xset_clean Inv Inv Inv.

Tactic Notation "xset_R_core" constr(dom) ident(R) constr(i) := 
 set (R := fun (t : dom) => \[] : hhprop (labeled dom));
  repeat match goal with 
  | |- context[hbig_fset _ _ ?f] =>
    match f with 
    | context[(i, 0)] =>
      let f' := fresh "f" in 
      set (f' := f);
      let R' := fresh "R" in 
      let t := eval unfold R in R in 
      (* idtac t; *)
      match t with 
      | (fun _ => \[]) => set (R' := f)
      | _  => set (R' := fun d => f d \* R d)
      end;
      unfold R in R';
      clear R; rename R' into R
    | _ => fail
    end
  end.

Tactic Notation "xset_R" constr(dom) ident(Inv) ident(R) constr(i) := 
  xset_R_core dom R i; xset_clean R R Inv.

Tactic Notation "xfor_sum_cong_solve2" constr(op) :=
  let hvE1 := fresh "hvE1" in
  let hvE2 := fresh "hvE2" in
  let someindom := fresh "someindom" in
  intros ???? hvE1 hvE2;  (try case_if=> //; [ ]);  
  rewrite ?/op; indomE;
  match goal with 
  | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ?; indomE; intros someindom; extens; intros 
  | _ => idtac
  end; try (rewrite hvE1 1?hvE2;
  [eauto|autorewrite with indomE; try math; 
    (first [ apply someindom | idtac ])| autorewrite with indomE; try math; 
    (first [ apply someindom | idtac ])]; simpl; try lia).

Tactic Notation "xfor_arrayset" constr(Inv) constr(R) constr(R') constr(op) constr(f) constr(s) :=
  eapply (@xfor_lemma_gen_array_fun_normal _ _ Inv R R' _ _ _ s f op);
  [ intros ??; rewrite ?/Inv ?/R ?/R';
    xnsimpl
  | 
  |
  |
  | xfor_sum_cong_solve op
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
  ]=> //; try (solve [ rewrite ?/Inv ?/R ?/R' /=; xlocal ]); autos*; try math.

Tactic Notation "xfor_arrayset" constr(Inv) constr(R) constr(R') constr(op) constr(f) constr(s) constr(idx) :=
  eapply (@xfor_lemma_gen_array_fun _ _ Inv R R' _ _ _ s f op idx);
  [ try math
  |
  |
  | intros ??; rewrite ?/Inv ?/R ?/R';
    xnsimpl
  |
  |
  |
  | xfor_sum_cong_solve op
  |
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
  ]=> //; try (solve [ rewrite ?/Inv ?/R ?/R' /=; xlocal ]); autos*; try math.

Tactic Notation "xfor_arrayset" constr(Inv) constr(R1) constr(R1') constr(R2) constr(R2') constr(op) constr(f) constr(s) :=
  eapply (@xfor_lemma_gen_array_fun_normal2 _ _ Inv R1 R1' R2 R2' _ _ _ _ s f op);
  [ intros ??; rewrite ?/Inv ?/R1 ?/R1' ?/R2 ?/R2'; xnsimpl
  |
  |
  |
  |
  |
  | xfor_sum_cong_solve2 op
  |
  |
  |
  |
  |
  |
  |
  |
  |
  |
  | rewrite ?/Inv ?/R1 /R2; rewrite -> ?hbig_fset_hstar; xsimpl
  | intros ?; rewrite ?/Inv ?/R1 /R2 ?/op; rewrite -> ?hbig_fset_hstar; xsimpl
  ]=> //; try (solve [ rewrite ?/Inv ?/R1 ?/R1' ?/R2 ?/R2' /=; xlocal ]); autos*; try math.

Tactic Notation "xfor_arrayset" constr(Inv) constr(R1) constr(R1') constr(R2) constr(R2') constr(op) constr(f) constr(s) constr(idx) :=
  eapply (@xfor_lemma_gen_array_fun2 _ _ Inv R1 R1' R2 R2' _ _ _ _ s f op idx);
  [ try math
  | 
  | 
  | intros ??; rewrite ?/Inv ?/R1 ?/R1' ?/R2 ?/R2'; xnsimpl
  |
  |
  |
  |
  |
  | xfor_sum_cong_solve2 op
  |
  |
  |
  |
  | 
  |
  |
  |
  |
  |
  |
  |rewrite ?/Inv ?/R1 ?/R2; rewrite -> ?hbig_fset_hstar; xsimpl
  | intros ?; rewrite ?/Inv ?/R1' ?/R2' ?/op; rewrite -> ?hbig_fset_hstar; xsimpl
  ]=> //; try (solve [ rewrite ?/Inv ?/R1 ?/R1' ?/R2 ?/R2' /=; xlocal ]); autos*; try math.
