From SLF Require Export LibCore.
From SLF Require Export LibSepFmap.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Definition upd {A B : Type} (f : A -> B) x y :=
  fun z => If x = z then y else f z.

Lemma upd_eq A B (f : A -> B) x y : 
  upd f x y x = y.
Proof. by apply: If_l. Qed.

Lemma upd_neq A B (f : A -> B) x y z : 
  z <> x ->
  upd f x y z = f z.
Proof. by move=>H; apply: If_r=>g'; subst z. Qed.

Definition uni {A B : Type} (fs : fset A) (f : A -> B) (g : A -> B) :=
  fun z => If indom fs z then f z else g z.

Notation "f '\u_' fs " := (uni fs f) (at level 10, left associativity).

Lemma uni_in A B {f g : A -> B} {x fs} : 
  indom fs x ->
  uni fs f g x = f x.
Proof. by move=>H; apply: If_l. Qed.

Lemma uni0 A B (f g : A -> B) : 
  uni empty f g = g.
Proof. by apply:fun_ext_1=>x; apply: If_r. Qed.

Lemma uni_upd A B (f g : A -> B) x fs :
  ~ indom fs x ->
  uni (update fs x tt) f g = upd (uni fs f g) x (f x).
Proof.
  move=>H; rewrite /update /upd/uni.
  apply: fun_ext_1=>z.
  have T: isTrue (x = z) -> x = z by apply istrue_isTrue_forw.
  rewrite -!if_isTrue.
  case:ifP=>H1; case:ifP=> H2; rewrite indom_union_eq isTrue_or /or in H1; 
                           first by move:H2=>/T->.
  - case: ifP=>//H3; case: ifP H1=>[|_]; last by case:ifP H3=>// /istrue_isTrue_forw.  
    move/istrue_isTrue_forw; rewrite indom_single_eq=>?; subst z. 
    by rewrite isTrue_eq_false_eq in H2. 
  - case: ifP H1; rewrite indom_single_eq=>//.
    + by move:H2=> /istrue_isTrue_forw->; rewrite isTrue_eq_false_eq.
  case: ifP=>// /istrue_isTrue_forw H3.
  case: ifP H1=>//; rewrite isTrue_eq_false_eq indom_single_eq=> H1.
  by case: ifP=>//; rewrite isTrue_eq_false_eq.
Qed.

Lemma uni_nin A B (f g : A -> B) x fs : 
  ~ indom fs x ->
  uni fs f g x = g x.
Proof.
  move=>H; rewrite /uni -!if_isTrue.
  by case: ifP=>//; move/istrue_isTrue_forw. 
Qed.

Lemma uniA A B (f1 f2 g : A -> B) fs1 fs2 : 
  uni fs1 f1 (uni fs2 f2 g) = 
  uni (fs1 \+ fs2) (uni fs1 f1 f2) g.
Proof.
  rewrite /uni; apply/fun_ext_1=> x.
  do ? case: classicT=>//; rewrite indom_union_eq=>H1; last by case: H1.  
  - by move=>?; case:H1; left. 
  - by move=>? ?; case: H1; right.   
Qed.  
   
Lemma upd_upd A B (f : A -> B) x y z w : 
  x <> z -> 
  upd (upd f x y) z w = upd (upd f z w) x y.
Proof.
  move=>H; rewrite /upd; apply:fun_ext_1=>v.
  case: classicT; case: classicT=>//.
  by move=><-?; subst z.
Qed.

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
Proof.
  rewrite /upd; apply:fun_ext_1=>z.
  by case: classicT=>//->.
Qed.
