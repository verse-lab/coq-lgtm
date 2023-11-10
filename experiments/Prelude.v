Set Implicit Arguments.
From LGTM.lib.theory Require Import LibReflect.
From LGTM.lib.seplog Require Import LibSepReference.
From mathcomp Require Import ssreflect ssrfun zify.

Ltac bool_rew := 
  rewrite ?false_eq_isTrue_eq ?istrue_isTrue_eq 
    ?true_eq_isTrue_eq -?(isTrue_and, isTrue_not, isTrue_or) ?not_isTrueE.

Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.

Coercion to_int : val >-> Z.
Coercion to_float : val >-> binary64.
Coercion to_loc : val >-> loc.
