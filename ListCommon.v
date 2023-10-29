From mathcomp Require Import seq ssrbool eqtype choice.
From SLF Require Import Sum Fun LabType Unary_IndexWithBounds.

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