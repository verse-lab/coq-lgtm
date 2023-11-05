From mathcomp Require Import seq ssrbool eqtype choice ssreflect ssrfun zify.
From SLF Require Import Sum Fun LabType.

Import List.

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

(* TODO change the name of this section *)
Section pure_facts.

Context {A : Type}.

Implicit Type l s : list A.
(* Implicit Type i : A. *)

Definition index (i : A) l : int. 
Proof using.
Admitted.
Lemma index_nodup (def : A) i l : 
  0 <= i < length l ->
  List.NoDup l -> 
    index (nth (abs i) l def) l = i.
Proof.
Admitted.

Lemma in_take x l i : 0 <= i <= length l -> (In x (take (abs i) l)) = (index x l < i).
Proof.
Admitted.

Lemma nth_index (def : A) x s : In x s -> nth (abs (index x s)) s def = x.
Admitted.

Lemma index_mem x s : (index x s < length s) = (In x s).
Admitted.

Lemma index_size x s : index x s <= length s.
Proof. Admitted.

Lemma indexG0 x s : 0 <= index x s.
Proof. Admitted.

Lemma memNindex x s :  ~In x s -> index x s = length s.
Admitted.

Definition list_interval (lb rb : nat) l :=
  take (rb - lb)%nat (drop lb l).

Lemma list_interval_length (lb rb : int) l :
  0 <= lb <= rb -> rb <= length l -> length (list_interval (abs lb) (abs rb) l) = rb - lb :> int.
Admitted.

Lemma list_interval_nth (def : A) (x lb rb : int) l :
  0 <= lb <= rb -> rb <= length l -> 0 <= x < rb - lb ->
  nth (abs (lb + x)) l def = nth (abs x) (list_interval (abs lb) (abs rb) l) def.
Admitted.

End pure_facts.

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