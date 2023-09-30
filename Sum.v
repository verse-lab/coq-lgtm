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

Lemma fset_of_list_nodup {A : Type} a (l : list A) : 
  List.NoDup l ->
  l = \U_(i <- interval 0 (length l)) `{List.nth (abs i) l a} :> fset _.
Admitted.

Lemma Sum0 {A} : @Sum A empty = fun=> 0.
Proof. unfold Sum. extens. intros F. rewrite -> (fst (@fset_foldE _ _ _ _)); auto. Qed.

Lemma SumUpdate {A : Type} (F : A -> int) (x : A) (fs : fset A) 
  (Hni : ~ indom fs x) :
  Σ_(i <- update fs x tt) F i = (Σ_(i <- fs) F i) + F x.
Proof.
  unfold Sum. rewrite -> (snd (@fset_foldE _ _ _ _)); auto. intros. math.
Qed. 

Lemma SumxSx F x y (H : x <= y) : Sum (interval x (y + 1)) F = Sum (interval x y) F + F y.
Proof.
  rewrite -> intervalUr. 2: math. rewrite SumUpdate; auto. 
  rewrite indom_interval; intros ?; math.
Qed.

Lemma SumEq {A : Type} F G (fs : fset A) :
  (forall x, indom fs x -> F x = G x) -> Sum fs F = Sum fs G.
Proof.
  intros.
  revert H. pattern fs. apply fset_ind; clear fs; intros.
  { by rewrite -> Sum0. }
  { rewrite ! SumUpdate; auto.
    rewrite H. 1: rewrite H1; auto.
    2: intros; apply H1.
    all: rewrite indom_update_eq; auto.
  }
Qed.


Lemma SumIf {A : Type} (P : A -> Prop) fs F G : 
  (Σ_(i <- fs) If P i then F i else G i) = 
  Σ_(i <- fs ∩ P) F i + Σ_(i <- fs ∖ P) G i.
Proof using.
Admitted.

Lemma SumList {A : Type} a (l : list A) F :
  NoDup l ->
  Σ_(i <- l) F i = Σ_(i <- `[0, length l]) F (nth (abs i) l a) .
Proof.
Admitted.

Lemma SumConst {A} (fs : fset A) c :
  Σ_(i <- fs) c = c * (fmap_dom_size fs).
Proof.
  apply fset_ind with (fs:=fs).
  { unfold fmap_dom_size. 
    rewrite fmap_exact_dom_empty. simpl.
    rewrite Sum0; try math.
  }
  { intros.
    unfold fmap_dom_size in *.
    destruct (fmap_exact_dom fs0) as (l & HH), (fmap_exact_dom (update fs0 x tt)) as (l' & HH').
    simpl in H |- *.
    pose proof HH as Htmp.
    eapply supp_update with (y:=tt) in Htmp. 2: apply H0.
    eapply is_map_supp_lengtheq in HH'.
    2: apply Htmp.
    rewrite <- HH', -> SumUpdate, -> H; auto. simpl List.length. math.
  }
Qed.

Corollary Sum0s {A} (fs : fset A): @Sum A fs (fun=> 0) = 0.
Proof. rewrite SumConst. math. Qed.

Corollary SumConst_interval (x y : int) (H : x <= y) c :
  Σ_(i <- interval x y) c = c * (y - x).
Proof. 
  rewrite SumConst.
  pose proof (interval_exact_dom H) as (l & Hlen & HH).
  unfold fmap_dom_size.
  destruct (fmap_exact_dom _) as (l' & HH').
  simpl. erewrite is_map_supp_lengtheq. 3: apply HH. 2: auto.
  rewrite Hlen. math. 
Qed.

Lemma SumUnion {A : Type} (F : A -> int) (fs1 fs2 : fset A) 
  (Hdj : disjoint fs1 fs2) :
  Σ_(i <- fs1 \+ fs2) F i = (Σ_(i <- fs1) F i) + (Σ_(i <- fs2) F i).
Proof.
  revert fs2 Hdj.
  apply fset_ind with (fs:=fs1); intros.
  { rewrite union_empty_l Sum0. math. }
  { rewrite SumUpdate; auto.
    rewrite /update. 
    rewrite -> union_comm_of_agree with (h2:=fs).
    2: apply agree_fset.
    rewrite disjoint_union_eq_l in Hdj.
    destruct Hdj as (Hdj1 & Hdj2). 
    rewrite -> disjoint_comm, <- disjoint_single_of_not_indom' in Hdj1.
    rewrite union_assoc H.
    2:{
      rewrite disjoint_union_eq_r.
      split; rewrite disjoint_comm; [ now apply disjoint_single_of_not_indom | tauto ].
    }
    rewrite <- update_eq_union_single, -> SumUpdate; auto; try math.
  }
Qed.

Lemma SumCascade {A B : Type} (F : B -> int) (fs : fset A) (fsi : A -> fset B)
  (Hdj : forall i j, i <> j -> indom fs i -> indom fs j -> disjoint (fsi i) (fsi j)) :
  Σ_(i0 <- fs) Σ_(i1 <- fsi i0) F i1 = Σ_(i0 <- \U_(i1 <- fs) fsi i1) F i0.
Proof.
  revert fsi Hdj.
  apply fset_ind with (fs:=fs); intros.
  { now rewrite Union0 !Sum0. }
  { rewrite SumUpdate; auto. rewrite Union_upd_fset SumUnion.
    2:{
      rewrite disjoint_Union.
      intros q Hq. apply Hdj.
      1: intros ->; auto.
      all: rewrite indom_update_eq; auto.
    }
    rewrite H; try math.
    intros.
    apply Hdj; auto.
    all: rewrite indom_update_eq; auto.
  }
Qed.
