Set Implicit Arguments.
From LGTM.lib.theory Require Import LibReflect.
From mathcomp Require Import ssreflect ssrfun zify.

Ltac bool_rew := 
  rewrite ?false_eq_isTrue_eq ?istrue_isTrue_eq 
    ?true_eq_isTrue_eq -?(isTrue_and, isTrue_not, isTrue_or) ?not_isTrueE.
