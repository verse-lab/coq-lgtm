Set Implicit Arguments.
From mathcomp Require Import ssreflect seq ssrbool eqtype choice.
From SLF Require Import Sum Fun LabType Unary_IndexWithBounds LibSepFmap.

Import List.

Definition sorted (l : list int) : Prop. Admitted.
Definition max (l : list int) : int. Admitted.

Definition merge (l1 l2 : list int) : list int. Admitted.

Lemma In_merge l1 l2 x : In x (merge l1 l2) = (In x l1 \/ In x l2).
Proof. Admitted.

Lemma sorted_nodup l : sorted l -> NoDup l.
Admitted.

Lemma sorted_merge l1 l2 : sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Admitted.

Lemma sorted_max_size l i : 
  i + 1 = length l -> l[i] = max l.
Admitted.

Lemma max_sublist l1 l2 : 
  (forall x, In x l1 -> In x l2) -> max l2 >= max l1.
Admitted.

Lemma nth_le_max l i :
  i >= 0 ->
  sorted l ->
  l[i] >= max l -> i + 1 = length l.
Admitted.

Lemma sorted_le i j l :
  sorted l ->
  0 <= i < length l ->
  0 <= j < length l ->
    i < j -> l[i] < l[j].
Admitted.

Lemma max_takeS i l : 
  0 <= i < length l ->
  max (take (abs (i + 1)) l) = Z.max l[i] (max (take (abs i) l)).
Admitted.

Lemma In_lt x i l :
  0 <= i < length l - 1 ->
  sorted l ->
    In x l -> x < l[i+1] -> x <= l[i].
Admitted.

Lemma max_le x l : 
  In x l -> x <= max l.
Proof.
Admitted.

Lemma size_merge l1 l2: 
  length (merge l1 l2) >= Z.max (length l1) (length l2).
Proof.
Admitted.

Lemma max0 : max nil = -1.
Proof.
Admitted.

Lemma In_le_0 l x :
  sorted l -> In x l -> x >= l[0].
Admitted.

Lemma search (x : int) (l : list int) : int.
Admitted. (*find 0 (> x)*)

Lemma search_lt_nth l i x : 
  sorted l -> 
  0 <= i < length l ->
    (forall y, In y l -> y < l[i] -> y <= x) ->
    x < l[i] ->
    search x l = l[i].
Admitted.

Lemma search_nth l i : 
  sorted l -> 
  0 < i + 1 < length l ->
    search l[i] l = l[i + 1].
Admitted.

Lemma merge_nthS l1 l2 i :
  sorted l1 -> sorted l2 ->
  0 < i + 1 < length (merge l1 l2) ->
    (merge l1 l2)[i+1] = Z.min (search (merge l1 l2)[i] l1) (search (merge l1 l2)[i] l2).
Admitted.

Lemma merge_nth0 l1 l2 :
  length l1 > 0 ->
  length l2 > 0 ->
  (merge l1 l2)[0] = Z.min l1[0] l2[0].
Admitted.

Lemma NoDup_nthZ {A : Type} i j l (z : A): 
  NoDup l <->
  ((0<= i < Datatypes.length l) ->
  (0<= j < Datatypes.length l) -> nth (abs i) l z = nth (abs j) l z -> i = j).
Admitted.

Lemma in_combineE {A B : Type} (l : list A) (l' : list B) (x : A) (y : B) :
  In (x, y) (combine l l') = (In x l /\ In y l').
Admitted.

Fact Sum_list_interval  (f : int -> int) (a b : int) l:
  NoDup (list_interval (abs a) (abs b) l) ->
  Sum (list_interval (abs a) (abs b) l) f = 
  Sum `[a, b] (fun i => f l[i]).
Admitted.

Fact intr_list (a b : int) (l: list int) : 
  (forall x, In x l -> a <= x < b) ->
  `[a, b] ∩ l = l.
Admitted.

Lemma slice_fullE {A : Type} (l : list A) : 
  list_interval (abs 0) (abs (length l)) l = l.
Admitted.

Lemma Union_same {B C} (v : int) (f : fmap B C) : 
  v > 0 -> 
    Union `[0, v] (fun _ => f) = f.
Admitted.

Lemma in_interval_list {A : Type} (l : list A) lb rb x: 
   In x (list_interval lb rb l) -> In x l.
Proof.
Admitted.

Lemma interval_unionE (l : list int) N : 
  sorted l -> 
  max l = N ->
  `[0, N] = \U_(i <- `[0, length l -1]) `[l[i], l[i+1] ].
Admitted.

Lemma sorted_le_rev i j l :
  sorted l ->
  0 <= i < length l ->
  0 <= j < length l ->
    l[i] < l[j] -> i < j.
Admitted.

Lemma sorted_leq i j l :
  sorted l ->
  0 <= i < length l ->
  0 <= j < length l ->
    i <= j -> l[i] <= l[j].
Admitted.

Lemma max_merge l1 l2 : 
  sorted l1 -> 
  sorted l2 ->
    max (merge l1 l2) = Z.max (max l1) (max l2).
Proof.
Admitted.

Lemma search_nth_pred l i x : 
  sorted l -> 
  0 < i < length l ->
    l[i-1] <= x < l[i] ->
    search x l = l[i].
Admitted.

Lemma sorted_max_le l i : 
  0 <= i < length l ->
  sorted l ->
  l[i] >= max l -> i +1 = length l.
Admitted. 

Section search_pure_facts.

Import List.

Class IncreasingIntList (L : list int) := {
  IIL_L_first : List.nth (abs 0) L 0 = 0;
  IIL_L_notnil : (0 < length L);
  IIL_L_inc : forall (i j : int), 
    (0 <= i < length L) -> 
    (0 <= i < length L) -> 
    (i < j) -> 
    (List.nth (abs i) L 0 < List.nth (abs j) L 0)
}.

Context (L : list int) {H : IncreasingIntList L}.

Fact IIL_L_inc' : forall (i j : int), 
  (0 <= i < length L) -> 
  (0 <= j < length L) -> 
  (i <= j) -> 
  (List.nth (abs i) L 0 <= List.nth (abs j) L 0).
Proof.
  intros. destruct (Z.eqb i j) eqn:E.
  { rewrite -> Z.eqb_eq in E. subst i. reflexivity. }
  { rewrite -> Z.eqb_neq in E. assert (i < j) by math.
    match goal with |- (?a <= ?b) => enough (a < b); try math end. 
    apply IIL_L_inc; math.
  }
Qed.
(*
Fact IIL_L_last : (abs (length L - 1)) = (abs (length L - 1)%nat).
Proof. pose proof IIL_L_notnil. math. Qed.

Hint Rewrite IIL_L_last : rew_maths.
*)
Variable (N : int).
Hypothesis H_L_last : List.nth (abs (length L - 1)) L 0 = N.  (* add abs to keep consistent *)

Fact IIL_zero_le_N : (0 <= N).
Proof.
  rewrite <- IIL_L_first, <- H_L_last.
  pose proof IIL_L_notnil.
  apply IIL_L_inc'; math.
Qed.

Fact IIL_L_bounded_impl (i a : int) 
  (Ha1 : (0 <= a < (length L - 1))) (Ha2 : (List.nth (abs a) L 0 <= i < List.nth (abs (a + 1)) L 0)) :
  0 <= i < N.
Proof.
  split.
  { transitivity (nth (abs a) L 0); try math.
    rewrite <- IIL_L_first at 1.
    apply IIL_L_inc'; math.
  }
  { enough (nth (abs (a + 1)) L 0 <= N) by math.
    subst N.
    apply IIL_L_inc'; math.
  }
Qed.

Fact search_exists j (Hj : (0 <= j < N)) :
  sig (fun a => (0 <= a < (length L - 1)) /\ (List.nth (abs a) L 0 <= j < List.nth (abs (a + 1)) L 0)).
Proof.
  destruct (Nat.leb (length L) 1) eqn:Ej.
  1:{ 
    apply Nat.leb_le in Ej. 
    pose proof IIL_L_notnil.
    assert (length L = 1%nat) as E by math.
    pose proof H_L_last as HH.
    rewrite E IIL_L_first in HH.
    math.
  }
  apply Nat.leb_gt in Ej.
  remember (abs j) as n eqn:En.
  revert j Hj En.
  induction n; intros.
  { assert (j = 0) as -> by math.
    exists 0. split; try math.
    split. 1: now rewrite IIL_L_first.
    rewrite <- IIL_L_first at 1.
    apply IIL_L_inc; math.
  }
  { assert (n = abs (j - 1)) as H1 by math.
    assert (0 <= j - 1 < N) as H2 by math.
    specialize (IHn _ H2 H1).
    destruct IHn as (a & Ha1 & Ha2).
    (* TODO relation with the imperative program? *)
    destruct (Z.leb (List.nth (abs (a + 1)) L 0) j) eqn:E.
    { apply Z.leb_le in E.
      assert (a + 1 < (length L - 1)) as Hlt.
      { destruct (Z.leb (length L - 1) (a + 1)) eqn:E'.
        2: apply Z.leb_gt in E'; math.
        apply Z.leb_le in E'.
        assert (a + 1 = (length L - 1)) as EE by math.
        rewrite EE in E.
        math.
      }
      assert (j = List.nth (abs (a + 1)) L 0) as -> by math.
      exists (a+1).
      split; [ math | split; [ math | apply IIL_L_inc; math ] ].
    }
    { apply Z.leb_gt in E.
      exists a.
      split; [ assumption | math ].
    }
  }
Qed.

Fact search_unify j (Hj : (0 <= j < N))
  a (Ha1 : (0 <= a < (length L - 1))) (Ha2 : (List.nth (abs a) L 0 <= j < List.nth (abs (a + 1)) L 0))
  a' (Ha1' : (0 <= a' < (length L - 1))) (Ha2' : (List.nth (abs a') L 0 <= j < List.nth (abs (a' + 1)) L 0)) :
  a = a'.
Proof.
  destruct (Z.leb (a'+1) a) eqn:Eu.
  { rewrite -> Z.leb_le in Eu.
    enough (List.nth (abs (a' + 1)) L 0 <= List.nth (abs a) L 0) by math.
    apply IIL_L_inc'; math.
  }
  { destruct (Z.leb (a+1) a') eqn:Eu'.
    { rewrite -> Z.leb_le in Eu'.
      enough (List.nth (abs (a + 1)) L 0 <= List.nth (abs a') L 0) by math.
      apply IIL_L_inc'; math.
    }
    { rewrite -> Z.leb_gt in Eu, Eu'. math. }
  }
Qed.

Lemma IILG0 i : L[i] >= 0.
Proof.
Admitted.

Lemma IIL_sorted : sorted L.
Proof.
Admitted.

Section segmentation.

Definition ind_seg (i : int) := 
  interval (List.nth (abs i) L 0) (List.nth (abs (i + 1)) L 0).

Lemma interval_segmentation_pre i :
  (0 <= i < (length L)) -> 
  Union (interval 0 i) ind_seg = interval 0 (List.nth (abs i) L 0).
Proof. 
  remember (to_nat i) as n.
  revert i Heqn.
  induction n as [ | n IH ]; intros.
  { assert (i = 0) as -> by math. 
    rewrite -> IIL_L_first. simpl. rewrite -> intervalgt; try math.
    by rewrite -> Union0.
  }
  { assert (i = n + 1) as -> by math.
    rewrite -> intervalUr; try math.
    rewrite -> Union_upd_fset, -> IH; try math.
    unfold ind_seg. 
    rewrite <- interval_union with (x:=0) (y:=(List.nth (abs n) L 0))
      (z:=(List.nth (abs (n + 1)) L 0)); try math.
    2:{
      rewrite <- IIL_L_first at 1. 
      destruct n; try math. 
      apply IIL_L_inc'; math. 
    }
    2: apply IIL_L_inc'; math. 
    rewrite -> union_comm_of_disjoint. 1: reflexivity.
    apply disjoint_of_not_indom_both.
    intros. rewrite -> indom_interval in *. math.
  }
Qed.

Lemma ind_seg_disjoint (i j : int) (Hi : indom (interval 0 (length L - 1)) i)
  (Hj : indom (interval 0 (length L - 1)) j) (Hn : i <> j) : disjoint (ind_seg i) (ind_seg j).
Proof.
  unfold ind_seg. 
  rewrite -> indom_interval in Hi, Hj.
  destruct Hi as (Hi1 & Hi2), Hj as (Hj1 & Hj2).
  apply disjoint_of_not_indom_both.
  intros x Hi Hj. rewrite -> indom_interval in Hi, Hj.
  destruct (Z.leb (i + 1) j) eqn:E.
  { rewrite -> Z.leb_le in E.
    apply IIL_L_inc' in E; try math.
  }
  { destruct (Z.leb (j + 1) i) eqn:E'.
    { rewrite -> Z.leb_le in E'.
      apply IIL_L_inc' in E'; try math.
    }
    rewrite -> Z.leb_gt in E, E'.
    math.
  }
Qed.

Lemma interval_segmentation :
  Union (interval 0 (length L - 1)) ind_seg = interval 0 N.
Proof.
  rewrite -> interval_segmentation_pre with (i:=(length L - 1)). 2: pose proof IIL_L_notnil; math.
  now subst N.
Qed.

End segmentation.

End search_pure_facts.
