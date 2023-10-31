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

Fact intr_list (a b : int) (l: list int) : 
  (forall x, In x l -> a <= x < b) ->
  `[a, b] ∩ l = l.
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

Lemma SumList_fold_eq {A : Type} a (l : list A) F :
  fold_left Z.add (map F l) 0 = Σ_(i <- `[0, length l]) F (nth (abs i) l a) .
Proof.
  induction l as [ | x l IH ] using rev_ind; simpl.
	{ by rewrite intervalgt // Sum0. }
	{ rewrite -> ?List.app_length in *; simpl List.length in *.
		replace (Z.of_nat (_ + 1)%nat) with ((List.length l) + 1)%Z by math.
		rewrite -> map_app, -> intervalUr, -> SumUpdate, -> fold_left_app; try rewrite indom_interval; try math.
		simpl. f_equal.
		{ rewrite IH. apply SumEq=> i Hi. rewrite indom_interval in Hi. rewrite app_nth1 //; try math. }
		{ replace (abs _) with (List.length l)%nat by math. by rewrite nth_middle. } }
Qed.

Corollary SumList_fold_eq' (l : list int) :
  fold_left Z.add l 0 = Σ_(i <- `[0, length l]) l[i].
Proof. rewrite <- map_id at 1. by rewrite -> SumList_fold_eq with (a:=0). Qed.

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

Corollary SumIf {A : Type} (P : A -> Prop) fs F G : 
  (Σ_(i <- fs) If P i then F i else G i) = 
  Σ_(i <- fs ∩ P) F i + Σ_(i <- fs ∖ P) G i.
Proof using.
  rewrite <- fs_pred_part with (p:=P) at 1.
  rewrite SumUnion. 2: apply fs_pred_part_disj.
  f_equal; eapply SumEq; intros ? Hin; rewrite filter_indom in Hin; case_if; eqsolve.
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

Fact Sum_interval_change : forall (f : int -> int) (a b c : int),
  Sum (interval a b) f = Sum (interval (a + c) (b + c)) (fun i => f (i - c)).
Proof using. clear.
  intros.
  destruct (Z.leb b a) eqn:E.
  1:{ apply Z.leb_le in E. rewrite !intervalgt; try math. now rewrite Sum0. }
  apply Z.leb_gt in E. assert (a <= b) as E' by math. clear E.
  remember (abs (b - a)) as n eqn:E.
  revert E E'. revert a b. induction n as [ | n IH ]; intros.
  { rewrite !intervalgt; try math. now rewrite Sum0. }
  { rewrite -> intervalU with (x:=a); try math.
    rewrite -> intervalU with (x:=a+c); try math.
    rewrite !SumUpdate. 2-3: rewrite indom_interval; try math.
    f_equal. 2: f_equal; math.
    rewrite IH; try math. do 2 f_equal. math. }
Qed.
