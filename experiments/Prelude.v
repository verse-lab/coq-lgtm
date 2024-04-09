Set Implicit Arguments.
From LGTM.lib.theory Require Import LibReflect.
From LGTM.lib.seplog Require Import LibSepReference LibHypHeap LibWP LibXWP LibSepSimpl LibArray.
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

Notation "p '.+' i '|-(' l ',' x ')->' v" := (hsingle (p + 1 + abs i)%nat (LibLabType.Lab (l,0)%Z x) v) (at level 32, format  "p  .+  i  |-( l ,  x )->  v").

Notation "'arrf(' y ',' i 'in' N '=>' f ')⟨' l ',' d '⟩'" := 
  (harray_fun_int (fun i => f) y N (LibLabType.Lab (l,0) d)) (at level 32, i binder, format "arrf( y ,  i  in  N =>  f )⟨ l ,  d ⟩") : hprop_scope.

Notation "'arr(' x ',' y ')⟨`' d '⟩'" := 
  (harray_int y x d) (at level 32, format "arr( x ,  y )⟨` d ⟩") : hprop_scope.

Notation "s '[' i ']' ':=' x" := (val_array_set s i x) (in custom trm at level 50, format "s [ i ]  :=  x").
    
  