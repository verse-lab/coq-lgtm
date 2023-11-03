Set Implicit Arguments.
From SLF Require Import Fun LabType Sum ListCommon.
From SLF Require Import LibSepReference  LibWP LibSepSimpl Struct.
From SLF Require Import LibSepTLCbuffer Loops Struct2 Subst.
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
  rewrite -(lof_indices val_uninit) !(lof_indices' val_uninit) in HH |- *.
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

(* TODO possibly, reuse some parts from xfor_sum? *)
Global Tactic Notation "xfor_specialized_normal" constr(Inv) constr(R) uconstr(R') uconstr(op) uconstr(f) constr(s) :=
  eapply (@xfor_lemma_gen_array_fun_normal _ _ Inv R R' _ _ _ s f op);
  [ intros ??; rewrite ?/Inv ?/R ?/R';
    xnsimpl
  | 
  |
  |
  | let hvE := fresh "hvE" in
    let someindom := fresh "someindom" in
    intros ???? hvE; rewrite ?/op; indomE;
    match goal with 
    | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ?; indomE; intros someindom; extens; intros 
    | _ => idtac
    end; try setoid_rewrite hvE; [eauto|autorewrite with indomE; try math; 
      (first [ apply someindom | idtac ])]
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
  ]=> //; try (solve [ rewrite ?/Inv ?/R ?/R' /=; xlocal ]); autos*.

Tactic Notation "xfor_specialized" constr(Inv) constr(R) uconstr(R') uconstr(op) uconstr(f) uconstr(idx) constr(s) :=
  eapply (@xfor_lemma_gen_array_fun _ _ Inv R R' _ _ _ s f op idx);
  [ try math
  |
  |
  | intros ??; rewrite ?/Inv ?/R ?/R';
    xnsimpl
  | rewrite ?/Inv; try xlocal
  | rewrite ?/R; try xlocal
  | rewrite ?/R'; try xlocal
   | let hvE := fresh "hvE" in
     let someindom := fresh "someindom" in
     intros ???? hvE; (try case_if=> //; [ ]); 
     rewrite ?/op; indomE;
     match goal with 
     | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ?; indomE; intros someindom; extens; intros 
     | _ => idtac
     end; try (setoid_rewrite hvE; [eauto|autorewrite with indomE; try math; 
       (first [ apply someindom | idtac ])])
  |
  | 
  | try math
  |
  |
  |
  |
  |
  |
  | rewrite ?/Inv ?/R; rewrite -> ?hbig_fset_hstar; xsimpl
  | intros ?; rewrite ?/Inv ?/R' ?/op; rewrite -> ?hbig_fset_hstar; xsimpl
  ]=> //; autos*; try math.

Tactic Notation "xfor_specialized_normal2" constr(Inv) constr(R1) uconstr(R1') constr(R2) uconstr(R2') uconstr(op) uconstr(f) constr(s) :=
  eapply (@xfor_lemma_gen_array_fun_normal2 _ _ Inv R1 R1' R2 R2' _ _ _ _ s f op);
  [ intros ??; rewrite ?/Inv ?/R1 ?/R1' ?/R2 ?/R2'; xnsimpl
  | rewrite /Inv; xlocal
  | rewrite /R1; xlocal
  | rewrite /R1; xlocal
  | rewrite /R2; xlocal
  | rewrite /R2; xlocal
  | let hvE1 := fresh "hvE1" in
    let hvE2 := fresh "hvE2" in
    let someindom := fresh "someindom" in
    intros ???? hvE1 hvE2; rewrite ?/op; indomE;
    match goal with 
    | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ?; indomE; intros someindom; extens; intros 
    | _ => idtac
    end; try rewrite hvE1 1?hvE2;
     [eauto|autorewrite with indomE; try math; 
      (first [ apply someindom | idtac ])| autorewrite with indomE; try math; 
      (first [ apply someindom | idtac ])]; simpl; try lia
  |
  |
  |
  | try lia
  |
  |
  |
  |
  |
  |
  | rewrite ?/Inv ?/R1 /R2; rewrite -> ?hbig_fset_hstar; xsimpl
  | intros ?; rewrite ?/Inv ?/R1 /R2 ?/op; rewrite -> ?hbig_fset_hstar; xsimpl
  ]=> //; autos*.

Tactic Notation "xfor_specialized2" constr(Inv) constr(R1) uconstr(R1') constr(R2) uconstr(R2') uconstr(op) uconstr(f) uconstr(idx) constr(s) :=
  eapply (@xfor_lemma_gen_array_fun2 _ _ Inv R1 R1' R2 R2' _ _ _ _ s f op idx);
  [ try math
  | 
  | 
  | intros ??; rewrite ?/Inv ?/R1 ?/R1' ?/R2 ?/R2'; xnsimpl
  | rewrite ?/Inv; try xlocal
  | rewrite ?/R1; try xlocal
  | rewrite ?/R1'; try xlocal
  | rewrite ?/R2; try xlocal
  | rewrite ?/R2'; try xlocal
  | let hvE1 := fresh "hvE1" in
    let hvE2 := fresh "hvE2" in
    let someindom := fresh "someindom" in
    intros ???? hvE1 hvE2;  (try case_if=> //; [ ]);  
    rewrite ?/op; indomE;
    match goal with 
    | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ?; indomE; intros someindom; extens; intros 
    | _ => idtac
    end; try rewrite hvE1 1?hvE2;
    [eauto|autorewrite with indomE; try math; 
      (first [ apply someindom | idtac ])| autorewrite with indomE; try math; 
      (first [ apply someindom | idtac ])]; simpl; try lia
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
  ]=> //; autos*; try lia.