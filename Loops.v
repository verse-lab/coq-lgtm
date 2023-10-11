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
  do 2 f_equal; rewrite (opP _ hr) ?E0 ?Z.add_0_r; 
  [apply/SumEq=> ??; apply/opP|]=> ? IN*; rewrite /uni indom_Union; case: classicT=> //.
  { case; eexists; splits*; rewrite indom_label_eq; autos*. }
  case=> l' []/[!@indom_label_eq]/[!indom_interval]=> ?.
  case=> _ /disjoint_inv_not_indom_both /(_ IN)-[].
  apply/Dj; lia.
Qed.

Lemma xwhile_big_op_lemma_aux2 `{INH: Inhab D} Inv (R1 R2 R1' R2' : Dom.type -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1 fsi2
  Z N (C1 C2 : Dom.type -> trm) (i j k : int) (C T : trm) b0
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
      false @disjoint_inv_not_indom_both. 2: apply H. 2: apply H0.
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

Lemma xwhile_big_op_lemma2 `{INH: Inhab D} Inv (R1 R2 R1' R2' : Dom.type -> hhprop) 
  (op : (D -> val) -> int -> int) p 
  s fsi1 fsi2
  Z N (C1 C2 : Dom.type -> trm) (i j k : int) (C C' T : trm) b0
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


Lemma xfor_lemma2_hbig_op `{ID : Inhab D}
  Inv 
  (R1 R1' R2 R2' : Dom.type -> hhprop)
  m vd (H : int -> hhprop) (H' : int -> (D -> val) -> hhprop)
  s fsi1 fsi2 vr
  (N: Z) (C1 C2 : Dom.type -> trm) (C : trm)
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
        (\*_(d <- ⟨(j,0)%Z, fsi2 l⟩) R2' d) \* 
        Q \(m, vd) H' l v }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall j : int, hlocal (H j) ⟨(i,0%Z), single s tt⟩) ->
  (forall (j : int) (v : D -> val), hlocal (H' j v) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : D, hlocal (R1 i) (single i tt)) ->
  (forall i : D, hlocal (R1' i) (single i tt)) ->
  (forall i : D, hlocal (R2 i) (single i tt)) ->
  (forall i : D, hlocal (R2' i) (single i tt)) ->
  (forall (hv hv' : D -> val) m,
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
  { move=> hv; apply/hbig_fset_eq=> d ?.
    apply/opP=> x ? /=; case: classicT=> // ; try lia.
    { by case: classicT=> // -[]; split=> //; rewrite -indom_interval. }
    case: classicT=> // _ ?; case: classicT=> // -[].
    by split=> //; rewrite -indom_interval. }
  apply/(
    wp_for_hbig_op_na_bis Inv 
      (fun d => If lab d = (j,0) then R1  d else R2  d)
      (fun d => If lab d = (j,0) then R1' d else R2' d)
      H (fun i hv => H' i (hv \o set2 i))  
      (fun d => ⟨(j,0%Z), fsi1 d⟩ \u ⟨(k,0%Z), fsi2 d⟩) Post fsi' fi gi g
      (fs' := ⟨(i, 0), single s tt⟩)
      (fs := ⟨(j, 0), \U_(i <- `[0, N]) fsi1 i⟩ \u ⟨(k, 0), \U_(i <- `[0, N]) fsi2 i⟩)
      (f := f)
      (* (fsi' := fsi') *)
  ); try eassumption.
  { rewrite -Union_union_fset hbig_fset_union //.
      { rewrite -?Union_label ?hstar_fset_Lab /=. 
        do ? case: classicT=> *; subst=> //; xsimpl*. }
      do 2 rewrite disjoint_Union=> ??. 
      rewrite disjoint_label. left=> -[]. lia. }
  { by rewrite -Union_union_fset ?Union_label. }
  { by case=> l d; rewrite indom_label_eq /= /htrm_of; case: classicT. }
  { by move=> *. }
  { by move=> ?; case: classicT. }
  { by move=> ?; case: classicT. }
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
      by rewrite H'E. }
      do 2 rewrite disjoint_Union=> ??. 
      rewrite disjoint_label. left=> -[]. lia. } 
  { move=> > hvP; apply/opP=> * /=; apply/hvP.
    all: rewrite indom_union_eq ?indom_label_eq; autos*. }
  move=> l Q ?; move: (IH l Q).
  rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
  rewrite union_empty_r => {}IH.
  have->: 
    (fun hr : D -> val =>
      Inv (l + 1) \*
      (\*_(d <- ⟨(j, 0), fsi1 l⟩ \u ⟨(k, 0), fsi2 l⟩)
          (If lab d = (j, 0) then R1' d else R2' d)) \*
      Q \(m, vd) H' l ((hr \o f) \o set2 l)) = 
    (fun v : D -> val => Inv (l + 1) \* (\*_(d <- ⟨(j, 0), fsi1 l⟩) R1' d) \* (\*_(d <- ⟨(j, 0), fsi2 l⟩) R2' d) \* Q \(m, vd) H' l v).
  { apply/fun_ext_1=> ?. 
    rewrite hbig_fset_union // .
    { rewrite -?Union_label ?hstar_fset_Lab /=.
      do ? case: classicT=> *; subst=> //.
      { xsimpl*. }
      rewrite ?hstar_assoc; do 4 fequals.
      apply/opP=> x ? /=; case: classicT=> // ?; try lia.
      { case: classicT=> // -[]; split=> //; lia. }
      case: classicT=> //.
      case: classicT=> // -[]. split=> //; lia. }
    do 2 rewrite disjoint_Union=> ??. 
    rewrite disjoint_single /= => -[]; lia. }
  rewrite hbig_fset_union //; first last.
  { do 2 rewrite disjoint_Union=> ??. 
    rewrite disjoint_single /= => -[]; lia. }
  rewrite -?Union_label ?hstar_fset_Lab /=.
  case: classicT=> // ?; case: classicT=> // [[]|?]; first lia.
  rewrite hstar_assoc.
  rewrite ?hstar_fset_Lab /= in IH.
  erewrite wp_ht_eq; first (apply/IH; lia).
  case=> l' ?; rewrite ?indom_union_eq ?indom_label_eq=> -[][][]??; subst.
  { rewrite uni_in ?indom_label_eq //= /htrm_of.
    case: classicT=> //; autos*. }
  { have?: (i, 0) <> (j, 0) by case.
    rewrite uni_nin ?indom_label_eq /= /htrm_of; autos*.
    do ? (case: classicT=> //=; autos* ).
    move=> [_]??[]; split=> //.
    rewrite indom_Union; setoid_rewrite indom_interval; do ? (eexists; eauto). }
  have?: (i, 0) <> (k, 0) by case; lia.
  have?: (j, 0) <> (k, 0) by case; lia.
  rewrite uni_nin ?indom_label_eq /= /htrm_of; autos*.
  do ? (case: classicT=> //=; autos* ).
  move=> [_]??[]; split=> //.
  rewrite indom_Union; setoid_rewrite indom_interval; do ? (eexists; eauto).
Qed.

Lemma ntriple_conseq_frame2 H2 H1 Q1 H Q fs_ht : 
  ntriple H1 fs_ht Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q -> ntriple H fs_ht Q.
Proof.
  rewrite /ntriple /nwp ?wp_equiv=> *.
  apply/htriple_conseq_frame; eauto.
Qed.

Lemma ntriple_conseq H1 Q1 H Q fs_ht : 
  ntriple H1 fs_ht Q1 ->
  H ==> H1 ->
  Q1 ===> Q -> ntriple H fs_ht Q.
Proof.
  rewrite /ntriple /nwp ?wp_equiv=> *.
  apply/htriple_conseq; eauto.
Qed.

Lemma union_merge (h1 h2 : hheap D): 
  disjoint h1 h2 ->
  h1 \u h2 = Fmap.merge (fun=> (fun=> 0 : val)) h1 h2.
Proof.
  case: h1 h2=> h1 ? []h2 ?.
  rewrite /disjoint /union /merge /map_disjoint /map_union /map_merge /=.
  move=> Dj. apply/make_eq=> x; move: (Dj x).
  by case=>->.
Qed.


Lemma hmerge_hstar : 
  hstar = hmerge (fun _ _ => 0) (fun=> False).
Proof.
  apply/fun_ext_2=> ??; extens=> ?; splits.
  { case/hstar_inv=> h1 [h2][?][?][?]->.
    exists h1 h2; splits*.
    { by rewrite -disjoint_valid_subst. }
    by rewrite union_merge. }
  rewrite /hmerge=> -[]h1[]h2[?][?][?]->.
  exists h1 h2; splits*.
  { by rewrite disjoint_valid_subst. }
  by rewrite union_merge // disjoint_valid_subst.
Qed.

Ltac xlocal := 
  repeat (intros; 
  match goal with 
  | |- hlocal (_ \* _) _ => apply hlocal_hstar
  | |- hlocal \[] _    => apply hlocal_hempty
  | |- hlocal (hexists _) _ => apply hlocal_hexists
  | |- hlocal (hsingle _ _ _) (single _ _) => apply hlocal_hsingle_single
  | |- hlocal (hsingle _ _ _) (label (Lab _ (single _ _))) => 
    rewrite label_single; apply hlocal_hsingle_single
  | |- hlocal (hpure _) _ => apply hlocal_hpure
  end).

Lemma ntriple_frame X H Q fs_ht H' Q' : 
  (H = H' X) ->
  (forall v, Q v = Q' X v) ->
  (H' X ==> (H' \[]) \* X) ->
  ((Q' \[]) \*+ X ===> Q' X) ->
  H' \[] ==> N-WP fs_ht {{ v, Q' \[] v }} ->
  {{ H }} fs_ht {{ v, Q v }}.
Proof.
Admitted.

Lemma hstar0E : hstar \[] = id.
Proof. apply/fun_ext_1; xsimpl. Qed.

Global Arguments ntriple_frame _ {_}.
  
Tactic Notation "xframe2" uconstr(QH) := 
  (try (xframe QH; [ ]));
  try (
    let Q := fresh "Q" in 
    let HEQ := fresh "Q" in 
    remember QH as Q eqn: HEQ;
    rewrite -?HEQ;
    eapply (@ntriple_frame Q); 
    [ let h := fresh "h" in 
      let f := fresh "h" in 
      match goal with |- ?x = ?y => set (h := x) end;
      pattern Q in h;
      set (f := fun _ => _) in h;
      simpl in h;
      rewrite /h;
      reflexivity
    | let h := fresh "h" in 
      let f := fresh "h" in 
      let v := fresh "h" in 
      intros v; 
      match goal with |- ?x = ?y => set (h := x) end;
      pattern Q, v in h;
      set (f := fun _ _ => _) in h;
      simpl in h;
      rewrite /h;
      reflexivity
    | simpl; try rewrite HEQ; xsimpl*
    | simpl=> ?;
      try (have->: forall f, (fun x : hheap _ => f x) = f by []);
      try (have->: forall f, (fun x : hheap D => f x) = f by []);
      try rewrite HEQ;
      xsimpl*
    | simpl; rewrite -> ?hstar0E
    ]; clear Q HEQ
  ).

Lemma xfor_lemma_gen2_bigstr `{ID : Inhab D}
  Inv 
  (R1 R1' R2 R2' : Dom.type -> hhprop)
  s fsi1 fsi2 vr H H'
  (N: Z) (C1 C2 : Dom.type -> trm) (C : trm)
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
        (\*_(d <- ⟨(j,0)%Z, fsi2 l⟩) R2' d) \* 
        H' l v }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall j : int, hlocal (H j) ⟨(i,0%Z), single s tt⟩) ->
  (forall (j : int) (v : D -> val), hlocal (H' j v) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : D, hlocal (R1 i) (single i tt)) ->
  (forall i : D, hlocal (R1' i) (single i tt)) ->
  (forall i : D, hlocal (R2 i) (single i tt)) ->
  (forall i : D, hlocal (R2' i) (single i tt)) ->
  (forall (hv hv' : D -> val) m,
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

Lemma xfor_lemma_gen2_array `{ID : Inhab D}
  Inv 
  (R1 R1' R2 R2' : Dom.type -> hhprop)
  s fsi1 fsi2 vr (arrl : loc) (arr1 : list int) arr2
  (N: Z) (C1 C2 : Dom.type -> trm) (C : trm)
  (i j k : Z)
  Pre Post: 
  (forall v, length (arr2 v) = N :> int) ->
  length arr1 = N :> int ->
  (forall (l : int), 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1 d) \* 
        (\*_(d <- ⟨(k,0)%Z, fsi2 l⟩) R2 d) \* 
        (arrl + 1 + abs l)%nat ~⟨(i,0)%Z, s⟩~> arr1[l] }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld};
        {k| ld in fsi2 l       => C2 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R1' d) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi2 l⟩) R2' d) \* 
        (arrl + 1 + abs l)%nat ~⟨(i,0)%Z, s⟩~> (arr2 v)[l] }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : D, hlocal (R1 i) (single i tt)) ->
  (forall i : D, hlocal (R1' i) (single i tt)) ->
  (forall i : D, hlocal (R2 i) (single i tt)) ->
  (forall i : D, hlocal (R2' i) (single i tt)) ->
  (forall (hv hv' : D -> val) m,
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    (forall i, indom (fsi2 m) i -> hv[`k](i) = hv'[`k](i)) ->
    (arr2 hv)[m] = (arr2 hv')[m]) ->
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
  move=> AL1 AL2 IH ????? hvE ?????????? PreH PostH.
  have AL : forall hv, Datatypes.length arr1 = Datatypes.length (arr2 hv).
  { move=> v; move: (AL1 v). lia. }
  apply/ntriple_conseq; last exact/PostH; eauto.
  rewrite /harray_int/harray/hheader ?length_map ?length_List_length.
  apply/(ntriple_conseq); [|exact: himpl_trans|move=> ?]; first last.
  { rewrite /harray_int/harray/hheader ?length_map ?length_List_length -AL.
    move=> ?; apply:applys_eq_init; reflexivity. }
  xframe2 (arrl ~⟨(i, 0%Z), s⟩~> val_header (length arr1)).
  xframe2 \[(arrl, (⟨(i, 0), s⟩)%arr) <> null (⟨(i, 0), s⟩)%arr].
  rewrite ?hcellsE.  
  eapply xfor_lemma_gen2_bigstr with 
  (H := fun l => (arrl + 1 + abs l)%nat ~⟨(i, 0%Z), s⟩~> arr1[l])
  (H' := fun l v => (arrl + 1 + abs l)%nat ~⟨(i, 0%Z), s⟩~> (arr2 v)[l])
  (R1 := R1) (R2 := R2) (R2' := R2') (R1' := R1'); try eassumption; autos*=> //.
  { xlocal. }
  { xlocal. }
  { move=> ??? hvE1 hvE2; erewrite hvE; eauto. }
  { rewrite AL2. xsimpl. }
  move=> ?. rewrite hcellsE AL1. xsimpl*.
Qed.

End WithLoops.