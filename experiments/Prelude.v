Set Implicit Arguments.
From LGTM.lib.theory Require Import LibReflect.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl.
From mathcomp Require Import ssreflect ssrfun zify.

Ltac bool_rew := 
  rewrite ?false_eq_isTrue_eq ?istrue_isTrue_eq 
    ?true_eq_isTrue_eq -?(isTrue_and, isTrue_not, isTrue_or) ?not_isTrueE.

Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.

Coercion to_int : val >-> Z.
Coercion to_float : val >-> binary64.
Coercion to_loc : val >-> loc.

Tactic Notation "xpointwise_build" uconstr(E) :=
  apply/htriple_val_eq/htriple_conseq;
  [|eauto|move=> ?]; rewrite -?hstar_fset_pure -?hbig_fset_hstar; first last; 
  first (move=> ?; apply: applys_eq_init; reflexivity);
  apply/htriple_union_pointwise=> [> -> //|??]; 
  rewrite -wp_equiv wp_single; xapp E=> //; try eauto; try intros; try subst;
  try xsimpl*.
