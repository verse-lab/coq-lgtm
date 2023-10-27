Set Implicit Arguments.
From SLF Require Import Fun LabType Sum.
From SLF Require Import LibSepReference  LibWP LibSepSimpl Struct.
From SLF Require Import LibSepTLCbuffer Loops Struct2.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Import List.

Open Scope Z_scope.

Section WithLoops.

(* Context {D : Type}. *)

Arguments disjoint_inv_not_indom_both {_ _ _ _ _}.

Context {Dom : Type}.

Local Notation D := (labeled Dom).
Local Notation hhprop := (hhprop D).

(* Definition eld : D -> Dom := el. *)

Definition eld := (@eld Dom).

Local Coercion eld : D >-> Dom.

Definition lof f N := projT1 (intlist_of_intfun f N).

Lemma nth_lof f N i  : 
  0 <= i < N -> (lof f N)[i] = f i.
Proof.
Admitted.

Lemma length_lof f N : 
  0 <= N ->
  length (lof f N) = N :> int.
Proof.
Admitted.


Lemma xfor_lemma_gen_array_fun_aux `{ID : Inhab D}
  Inv 
  (R R' : Dom -> hhprop)
  s fsi1 vr (arrl : loc) (f : int -> int) (g : _ -> _ -> int)
  ( N:int) (C1 : Dom -> trm) (C : trm)
  (i j : int)
  Pre Post: 
  (0 <= N) ->
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
    harray_fun f arrl N (Lab (i,0) s)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R' d) \* 
    harray_fun (g hv) arrl N (Lab (i,0) s) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For 0 N (trm_fun vr C)};
      {j| ld in Union `[0,N] fsi1 => C1 ld}
    }]
  {{ v, Post v }}. 
Proof.
  move=>? IH *.
  eapply xfor_lemma_gen_array with (R := R) (R' := R') (arr1 := lof f N) (arr2 := fun hv => lof (g hv) N); try eassumption.
  { by move=> ?; rewrite length_lof. }
  { exact/length_lof. }
  { move=> l P; rewrite nth_lof //.
    apply/ntriple_conseq; [| |move=> v; rewrite nth_lof//]; try exact:himpl_refl.
    exact/IH. }
  move=> *; rewrite ?nth_lof //; autos*.
Qed.

Lemma xfor_lemma_gen_array_fun `{ID : Inhab D}
  Inv 
  (R R' : Dom -> hhprop)
  s fsi1 vr (arrl : loc) (f : int -> int) (g : _ -> _ -> int)
  (N: Z) (C1 : Dom -> trm) (C C' : trm)
  (i j : Z)
  Pre Post: 
  (0 <= N) ->
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
    harray_fun f arrl N (Lab (i,0) s)) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union `[0,N] fsi1) R' d) \* 
    harray_fun (g hv) arrl N (Lab (i,0) s) ==>
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
  move: (H14 hv); rewrite wp_equiv=> ?.
  xapp=> hv'. rewrite -/(lab_fun_upd _ _ _).
  xsimpl (lab_fun_upd hv' hv (i, 0))=> ?.
  apply: applys_eq_init; fequals; apply/fun_ext_1=> /=.
  case=> l x.
  rewrite /uni ?indom_label_eq; case: classicT.
  { by case=> <- /=; rewrite lab_eqb_sym E. }
  case: classicT=> //.
  case=> <- /=; rewrite eqbxx //.
Qed.


End WithLoops.