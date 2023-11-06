Set Implicit Arguments.
From SLF Require Import Fun LabType Sum ListCommon.
From SLF Require Import LibSepReference LibWP LibSepSimpl Struct Loops Struct2 Loops2.
From SLF Require Import LibSepTLCbuffer.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Import List.

Open Scope Z_scope.

Section WithLoops.

Context {Dom : Type}.

Local Notation D := (labeled Dom).
Local Notation hhprop := (hhprop D).

(* Definition eld : D -> Dom := el. *)

Definition eld := (@eld Dom).

Local Coercion eld : D >-> Dom.

Lemma xfor_big_op_lemma_aux_extended `{INH: Inhab D} {A B : Type} Inv (R R' : Dom -> hhprop) 
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

Lemma xfor_big_op_lemma_extended `{Inhab D} {A B : Type} Inv (R R' : Dom -> hhprop) 
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
  apply/(xfor_big_op_lemma_aux_extended Inv R R' toval a0 bdef); eauto.
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

(* the original xfor lemma can be recovered *)
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
  apply/(xfor_big_op_lemma_extended Inv R R' val_int 0 0 Z.add (fun=> True)); eauto.
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

End WithLoops.

Tactic Notation "xfor_sum_float" constr(Inv) constr(R) uconstr(R') uconstr(op) constr(s) :=
  eapply (@xfor_big_op_lemma_extended _ _ _ _ Inv R R' val_float float_unit float_unit (@BPLUS _ Tdouble) op s);
  [ let L := fresh in 
    intros ?? L;
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

Tactic Notation "xfor_sum_fma" constr(Inv) constr(R) uconstr(R') uconstr(op) constr(s) :=
  eapply (@xfor_big_op_lemma_extended _ _ _ _ Inv R R' val_float float_unit (float_unit, float_unit) (fun a (b : binary64 * binary64) => @BFMA _ Tdouble b.1 b.2 a) 
    (fun (b : binary64 * binary64) => @finite Tdouble b.1 /\ @finite Tdouble b.2) op s);
  [ let L := fresh in 
    intros ?? L;
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
