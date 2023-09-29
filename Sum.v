Set Implicit Arguments.
From SLF Require Import Fun LabType LibSepFmap.
From mathcomp Require Import ssreflect ssrfun zify.
From Coq Require Import List.

Notation "x '[' i ']'" := (List.nth (abs i) x 0) (at level 5, format "x [ i ]").

Definition Sum {A : Type} (fs : fset A) (f : A -> int) : int :=
  fset_fold 0 (fun idx acc => acc + (f idx)) fs.
Reserved Notation "'Σ_' ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' Σ_ ( i  <-  r ) '/  '  F ']'").

Notation "'Σ_' ( i <- r ) F" :=
  (Sum r (fun i => F)) : nat_scope.

Definition mem {A : Type} s := (List.In (A := A))^~ s.

Coercion mem : list >-> Funclass.

Definition fset_of_list {A : Type} (l : list A) : fset A. Admitted.

Coercion fset_of_list : list >-> fset.

Lemma fset_of_list_in {A : Type} (l : list A) : 
  (fun x => List.In x l) = indom (fset_of_list l).
Admitted.

Lemma fset_of_list_nodup (l : list int) : 
  List.NoDup l ->
  l = \U_(i <- interval 0 (length l)) `{l[i]} :> fset _.
Admitted.

Lemma Sum0 {A} : @Sum A empty = fun=> 0.
Proof. unfold Sum. extens. intros F. rewrite -> (fst (@fset_foldE _ _ _ _)); auto. Qed.

Lemma Sum0s {A} (fs : fset A): @Sum A fs (fun=> 0) = 0.
Proof.
Admitted.

Lemma SumxSx F x y (H : x <= y) : Sum (interval x (y + 1)) F = Sum (interval x y) F + F y.
Proof.
  unfold Sum. rewrite -> intervalUr. 2: math.
  rewrite -> (snd (@fset_foldE _ _ _ _)); auto. 
  math. rewrite indom_interval; intros ?; math.
Qed.

Lemma SumEq F G (fs : fset int) :
  (forall x, indom fs x -> F x = G x) -> Sum fs F = Sum fs G.
Proof.
  intros.
  revert H. pattern fs. apply fset_ind; clear fs; intros.
  { by rewrite -> Sum0. }
  { unfold Sum.
    rewrite -> ! (snd (@fset_foldE _ _ _ _)); try assumption; try math.
    fold (Sum fs F). fold (Sum fs G).
    rewrite -> H, -> H1. 1: reflexivity.
    1: apply indom_update.
    intros. apply H1. rewrite -> indom_update_eq. by right.
  }
Qed.


Lemma SumIf {A : Type} (P : A -> Prop) fs F G : 
  (Σ_(i <- fs) If P i then F i else G i) = 
  Σ_(i <- fs ∩ P) F i + Σ_(i <- fs ∖ P) G i.
Proof using.
Admitted.

Lemma SumList (l : list int) F :
  NoDup l ->
  Σ_(i <- l) F i = Σ_(i <- `[0, length l]) F l[i] .
Proof.
Admitted.