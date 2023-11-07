Set Implicit Arguments.
From mathcomp Require Import ssreflect ssrfun zify.
From SLF Require Import Fun LabType LibSepFmap.
From Coq Require Sorting.

Import List.

Notation "x '[' i ']'" := (List.nth (abs i) x 0) (at level 5, format "x [ i ]").

Fact take_conversion [A : Type] (n : nat) (l : list A) : take n l = firstn n l.
Proof.
  revert n. induction l; intros; simpl in *; rewrite ?take_nil; auto.
  all: destruct n; auto.
  simpl. rewrite ?take_cons. now rewrite IHl.
Qed.

Fact nth_error_some_inrange {A : Type} (i : nat) (al : list A) a : 
  nth_error al i = Some a -> i < length al.
Proof.
  revert i a. induction al as [ | a' al IH ]; intros; simpl in *.
  all: destruct i; simpl in *; try discriminate; try lia.
  apply IH in H. lia.
Qed.

Fact Forall2_nth_pointwise [A B : Type] (da : A) (db : B) (la : list A) (lb : list B) (P : A -> B -> Prop) :
  List.Forall2 P la lb <-> (List.length la = List.length lb /\ forall i : nat, (i < List.length la)%nat ->
    P (List.nth i la da) (List.nth i lb db)).
Proof.
  revert lb. induction la as [ | a la' IH ] using List.rev_ind; intros.
  { split; [ intros H | intros (Hl & HP) ].
    { inversion_clear H. simpl. split; auto. intros. lia. }
    { destruct lb; try discriminate. constructor. } }
  { split; [ intros H | intros (Hl & HP) ].
    { pose proof (List.Forall2_length H) as Hl. split; auto.
      apply List.Forall2_app_inv_l in H. destruct H as (lb' & bb & (_ & Hfeq)%IH & Hab & ->).
      inversion Hab; subst. inversion H3; subst. rename y into b.
      rewrite ?List.app_length /= ?Nat.add_1_r in Hl |- *. injection Hl as Hl.
      intros i Hi. destruct (Nat.ltb i (List.length la')) eqn:E.
      { apply Nat.ltb_lt in E. rewrite !List.app_nth1; try lia. now apply Hfeq. }
      { apply Nat.ltb_ge in E. assert (i = List.length lb') as -> by lia.
        rewrite <- Hl at 1. rewrite !List.nth_middle; try lia. assumption. } }
    { rewrite ?List.app_length /= ?Nat.add_1_r in Hl |- *.
      assert (lb <> nil) as (lb' & b & ->)%List.exists_last by (destruct lb; simpl in Hl; eqsolve).
      rewrite ?List.app_length /= ?Nat.add_1_r in Hl, HP. injection Hl as Hl.
      apply List.Forall2_app.
      { apply IH. split; auto. intros i Hi. specialize (HP _ (Peano.le_S _ _ Hi)).
        rewrite !List.app_nth1 in HP; try lia. exact HP. }
      { constructor. 2: constructor. specialize (HP _ (Peano.le_n _)).
        rewrite -> Hl in HP at 2. rewrite !List.nth_middle in HP; try lia. exact HP. } } }
Qed.

Fact nth_map_lt : forall [A B : Type] (da : A) (db : B) (f : A -> B) (l : list A) (n : nat)
  (H : (n < length l)%nat),
  nth n (map f l) db = f (nth n l da).
Proof.
  intros. revert l H. induction n as [ | n IH ]; intros.
  { destruct l; simpl in H; try lia; auto. }
  { destruct l; simpl in H; try lia; auto.
    simpl. apply IH. lia. }
Qed.

Fact nth_In_int (l : list int) (n : int) :
  (0 <= n < length l) -> In (nth (abs n) l 0) l.
Proof. intros H. apply nth_In. math. Qed.

Lemma NoDup_nthZ {A : Type} l (z : A): 
  NoDup l <->
  (forall i j, (0<= i < Datatypes.length l) ->
  (0<= j < Datatypes.length l) -> nth (abs i) l z = nth (abs j) l z -> i = j).
Proof. 
  etransitivity. 1: apply NoDup_nth with (d:=z). 
  split; intros H i j Ha Hb Hc. 
  { enough (abs i = abs j) by math. revert Hc. apply H; math. }
  { enough (Z.of_nat i = Z.of_nat j) by math. apply H; try math.
    replace (abs i) with i by math. replace (abs j) with j by math. assumption. }
Qed.

Lemma in_combineE {A B : Type} (l : list A) (l' : list B) (x : A) (y : B) :
  In (x, y) (combine l l') -> (In x l /\ In y l').
Proof.
  revert l'. induction l as [ | a l IH ]; simpl; intros; try tauto.
  destruct l' as [ | b l' ]; simpl in H |- *; try contradiction.  
  rewrite pair_equal_spec in H. firstorder.
Qed.

Section index.

Context {A : Type}.

Implicit Type l s : list A.
(* Implicit Type i : A. *)

Fixpoint index (i : A) l : int :=
  match l with
  | nil => 0
  | x :: l' => If x = i then 0 else (index i l' + 1)
  end.

Lemma index_nodup (def : A) i l : 
  0 <= i < length l ->
  List.NoDup l -> 
    index (nth (abs i) l def) l = i.
Proof.
  revert i. induction l as [ | x l IH ]; intros i Hi Hnodup; simpl in Hi |- *; try math.
  inversion_clear Hnodup.
  remember (abs i) as n eqn:E. destruct n.
  { case_if. math. }
  { replace n with (abs (i-1)) by math. rewrite IH; try math; auto. 
    case_if; try math.
    subst x. false H. apply nth_In. math. }
Qed.

Lemma index_mem x s : (index x s < length s) = (In x s).
Proof.
  induction s as [ | y s IH ]; simpl; try math. rewrite -IH. clear IH. case_if; extens; intuition lia.
Qed.

Lemma index_size x s : index x s <= length s.
Proof. induction s; simpl; auto; try case_if; try math. Qed.

Lemma indexG0 x s : 0 <= index x s.
Proof. induction s; simpl; auto; try case_if; try math. Qed.

Lemma nth_index (def : A) x s : In x s -> nth (abs (index x s)) s def = x.
Proof.
  induction s as [ | y s IH ]; simpl; intros; try contradiction. 
  case_if; auto. destruct H; try contradiction.
  pose proof (indexG0 x s).
  replace (abs (index x s + 1)) with (S (abs (index x s)))%nat by math. auto.
Qed.

Lemma index_app1 x s1 s2 : index x s1 < length s1 -> index x (List.app s1 s2) = index x s1.
Proof.
  induction s1 as [ | y s1 IH ]; simpl; intros; auto; try lia.
  case_if; auto. rewrite IH; math.
Qed.

Lemma index_app_le x s1 s2 : index x s1 <= index x (List.app s1 s2).
Proof.
  induction s1 as [ | y s1 IH ]; simpl; intros; auto; try lia.
  1: apply indexG0. case_if; try math.
Qed.

Corollary in_take x l i : 0 <= i <= length l -> (In x (take (abs i) l)) = (index x l < i).
Proof.
  intros Hi. pose proof (firstn_skipn (abs i) l).
  assert (length (firstn (abs i) l) = abs i :> nat) by (rewrite firstn_length_le; math).
  rewrite -> take_conversion. rewrite <- H at 2.
  extens. split; intros HH.
  { rewrite -index_mem in HH. rewrite index_app1; math. }
  { rewrite -index_mem H0. pose proof (index_app_le x (firstn (abs i) l) (skipn (abs i) l)). math. }
Qed.

Corollary memNindex x s :  ~In x s -> index x s = length s.
Proof. rewrite -index_mem. pose proof (index_size x s). math. Qed.

End index.

Section list_of_fun.

(* some customized theory of from functions to lists *)
Lemma list_of_fun [A : Type] (f : int -> A) (n : int) (H : 0 <= n) :
  @sigT (list A) (fun l =>
    (length l = n :> int /\ (forall (i : int) (def : A), 0 <= i < n -> nth (abs i) l def = f i))).
Proof.
  remember (abs n) as nn eqn:E.
  revert n H E. induction nn as [ | nn IH ]; intros.
  { assert (n = 0) as -> by math. exists (@nil A). split; auto. intros; math. }
  { assert (nn = abs (n - 1)) as Hq by math. apply IH in Hq; try math.
    destruct Hq as (la & H1 & H2). exists (app la (f (n - 1) :: nil)).
    rewrite -> app_length. split; simpl; try math.
    intros i def Hin. destruct (Z.leb (n - 1) i) eqn:E2.
    { apply Z.leb_le in E2. replace i with (n-1) in * by math. 
      replace (abs (n-1)) with (length la) by math. now rewrite nth_middle. }
    { apply Z.leb_gt in E2. rewrite app_nth1. 1: apply H2. all: math. } }
Qed.

Definition list_of_fun' [A : Type] (f : int -> A) (n : int) :
  @sigT (list A) (fun l =>
    (length l = abs n :> int /\ (forall (i : int) (def : A), 0 <= i < abs n -> nth (abs i) l def = f i))).
apply list_of_fun. math. Defined.

Fact lof_make_constfun [A : Type] (c : A) (n : int) :
  (projT1 (list_of_fun' (fun _ => c) n)) = repeat c (abs n).
Proof.
  destruct (list_of_fun' _ _) as (l & Hlen & HH). simpl.
  apply nth_ext with (d:=c) (d':=c).
  1: rewrite repeat_length; math.
  intros i Hi. 
  rewrite -> nth_repeat; try math. rewrite <- HH with (i:=i) (def:=c) at 2; try math.
  f_equal; math.
Qed.

(* TODO possibly change this name? *)
Definition lof f N := projT1 (@list_of_fun' int f N).

Lemma nth_lof f N i : 
  0 <= i < abs N -> nth (abs i) (lof f N) 0 = f i.
Proof. unfold lof. destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl. auto. Qed.

Lemma nth_lof' f N i :
  0 <= N -> 0 <= i < N -> nth (abs i) (lof f N) 0 = f i.
Proof. intros ??. apply nth_lof. math. Qed.

Lemma length_lof f N : 
  0 <= N -> length (lof f N) = N :> int.
Proof. unfold lof. destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl. math. Qed.

Lemma length_lof' f N : 
  length (lof f N) = abs N :> nat.
Proof. unfold lof. destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl. math. Qed.

Lemma In_lof_id N a : In a (lof id N) <-> 0 <= a < abs N.
Proof.
  unfold lof. destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
  split; intros H.
  { apply In_nth with (d:=0) in H. destruct H as (n & Hlt & <-).
    replace n with (abs n) by math. rewrite Hl1; math. }
  { pose proof H as HH%(Hl1 _ 0). rewrite -HH. apply nth_In. math. }
Qed.

Lemma lof_indices {A : Type} (f : int -> A) (g : int -> int) n :
  projT1 (list_of_fun' (f \o g) n) = map f (lof g n).
Proof.
  destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
  pose proof (length_lof' g n) as Hlen2.
  apply (nth_ext _ _ (f 0) (f 0)). 
  1: rewrite map_length; math.
  intros n0 Hlt. replace n0 with (abs n0) by math.
  rewrite Hl1 ?(nth_map_lt 0) ?nth_lof //; try math.
Qed.

Corollary lof_indices' {A : Type} (f : int -> A) n :
  projT1 (list_of_fun' f n) = map f (lof id n).
Proof. by rewrite <- lof_indices. Qed.

End list_of_fun.

Section list_interval.

Context {A : Type}.

Implicit Type l : list A.

Definition list_interval (lb rb : nat) l :=
  firstn (rb - lb)%nat (skipn lb l).

Lemma list_interval_length (lb rb : int) l :
  0 <= lb <= rb -> rb <= length l -> length (list_interval (abs lb) (abs rb) l) = rb - lb :> int.
Proof. intros. rewrite /list_interval firstn_length_le ?skipn_length; try math. Qed.

Lemma list_interval_nth (def : A) (x lb rb : int) l :
  0 <= lb <= rb -> rb <= length l -> 0 <= x < rb - lb ->
  nth (abs (lb + x)) l def = nth (abs x) (list_interval (abs lb) (abs rb) l) def.
Proof.
  intros. rewrite /list_interval.
  pose proof (firstn_skipn (abs lb) l) as HH1.
  rewrite <- HH1 at 1. rewrite app_nth2. all: rewrite firstn_length_le; try math.
  replace (abs _ - abs _)%nat with (abs x) by math.
  remember (skipn _ _) as l' eqn:E.
  pose proof (firstn_skipn (abs rb - abs lb) l') as HH2.
  rewrite <- HH2 at 1. rewrite app_nth1; auto. 
  rewrite firstn_length_le; try math. subst l'; rewrite skipn_length; math.
Qed.

Corollary list_interval_nth' (def : A) (x lb rb : int) l :
  0 <= lb -> rb <= length l -> lb <= x < rb ->
  nth (abs (x - lb)) (list_interval (abs lb) (abs rb) l) def = nth (abs x) l def.
Proof. intros. rewrite -list_interval_nth; try math. f_equal; math. Qed.

Lemma slice_fullE l : list_interval (abs 0) (abs (length l)) l = l.
Proof. 
  rewrite /list_interval. etransitivity. 2: apply firstn_all.
  simpl. f_equal. math.
Qed. 

Lemma in_interval_list l lb rb x :
  In x (list_interval lb rb l) -> In x l.
Proof.
  rewrite /list_interval. intros. 
  rewrite -(firstn_skipn lb l) in_app_iff. right.
  rewrite -(firstn_skipn (rb - lb)%nat (skipn lb l)) in_app_iff. tauto.
Qed.

End list_interval.

Section sorted_max.

Definition sorted (l : list int) : Prop :=
  forall (i j : int), 
    (0 <= i < length l) -> 
    (0 <= i < length l) -> 
    (i < j) -> l[i] < l[j].

Definition max (l : list int) : int. Admitted.

Lemma sorted_nodup l : sorted l -> NoDup l.
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

Lemma max0 : max nil = -1.
Proof.
Admitted.

Lemma In_le_0 l x :
  sorted l -> In x l -> x >= l[0].
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

Lemma sorted_max_le l i : 
  0 <= i < length l ->
  sorted l ->
  l[i] >= max l -> i +1 = length l.
Admitted. 

Lemma interval_unionE (l : list int) N : 
  sorted l -> 
  max l = N ->
  `[0, N] = \U_(i <- `[0, length l -1]) `[l[i], l[i+1] ].
Admitted.

End sorted_max.

Section merge.

Definition merge (l1 l2 : list int) : list int. Admitted.

Lemma In_merge l1 l2 x : In x (merge l1 l2) = (In x l1 \/ In x l2).
Proof. Admitted.

Lemma sorted_merge l1 l2 : sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Admitted.

Lemma size_merge l1 l2: 
  length (merge l1 l2) >= Z.max (length l1) (length l2).
Proof.
Admitted.

Lemma merge_nth0 l1 l2 :
  length l1 > 0 ->
  length l2 > 0 ->
  (merge l1 l2)[0] = Z.min l1[0] l2[0].
Admitted.

Lemma max_merge l1 l2 : 
  sorted l1 -> 
  sorted l2 ->
    max (merge l1 l2) = Z.max (max l1) (max l2).
Proof.
Admitted.

End merge.

Section search_leastupperbound.

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

Lemma search_nth_pred l i x : 
  sorted l -> 
  0 < i < length l ->
    l[i-1] <= x < l[i] ->
    search x l = l[i].
Admitted.

End search_leastupperbound.

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

