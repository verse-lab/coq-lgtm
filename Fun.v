From SLF Require Export LibCore.
From SLF Require Export LibSepFmap.

From mathcomp Require Import ssreflect ssrfun.

Definition upd {A B : Type} (f : A -> B) x y :=
  fun z => If x = z then y else f z.

Lemma upd_eq A B (f : A -> B) x y : 
  upd f x y x = y.
Proof.
Admitted.

Lemma upd_neq A B (f : A -> B) x y z : 
  z <> x ->
  upd f x y z = f z.
Proof.
Admitted.

Definition uni {A B : Type} (fs : fset A) (f : A -> B) (g : A -> B) :=
  fun z => If indom fs z then f z else g z.

Notation "f '\u_' fs " := (uni fs f) (at level 10, left associativity).

Lemma uni_in A B {f g : A -> B} {x fs} : 
  indom fs x ->
  uni fs f g x = f x.
Proof.
Admitted.

Lemma uni0 A B (f g : A -> B) : 
  uni empty f g = g.
Proof.
Admitted.

Lemma uni_upd A B (f g : A -> B) x fs :
  ~ indom fs x ->
  uni (update fs x tt) f g = upd (uni fs f g) x (f x).
Proof.
Admitted.

Lemma uni_nin A B (f g : A -> B) x fs : 
  ~ indom fs x ->
  uni fs f g x = g x.
Proof.
Admitted.

Lemma uniA A B (f1 f2 g : A -> B) fs1 fs2 : 
  uni fs1 f1 (uni fs2 f2 g) = 
  uni (fs1 \+ fs2) (uni fs1 f1 f2) g.
Proof.
  rewrite /uni; apply/fun_ext_1=> ?.
  do ? case: classicT=> //.
Admitted.

Lemma upd_upd A B (f : A -> B) x y z w : 
  x <> z -> 
  upd (upd f x y) z w = upd (upd f z w) x y.
Proof.
Admitted.

(* Definition fcomp A B C (f : A -> B) (g : C -> A) := fun x => f (g (x)). *)


Lemma upd_uni_update A B (f g : A -> B) (x : A) (y : B) fs : 
  ~ indom fs x ->
  upd f x y \u_ (update fs x tt) g = upd (f \u_fs g) x y.
Proof.
  move=> ND; apply/fun_ext_1=> z.
  case: (prop_inv (indom (update fs x tt) z)).
  { move=> /[dup]/(@uni_in _ _ _ _ _ _)->.
    rewrite indom_update_eq=> -[->/[! upd_eq]//|].
    move=> E. 
    by rewrite ?upd_neq ?uni_in //; move: E=>/[swap]->. }
   move=> /[dup]? E; rewrite indom_update_eq in E.
  rewrite upd_neq ? uni_nin; autos*.
Qed.

Lemma updE A B (f : A -> B) x :
  f = upd f x (f x).
Admitted.