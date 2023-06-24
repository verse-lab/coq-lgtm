(** * LibSepFmap: Appendix - Finite Maps *)

Set Implicit Arguments.
From SLF Require Import LibCore.

From mathcomp Require Import ssreflect ssrfun.

(* ################################################################# *)
(** * Representation of Finite Maps *)

(** This file provides a representation of finite maps, which may be used
    to represent the memory state of a program.

    - It implements basic operations such as creation of a singleton map,
       union of maps, read and update operations.
    - It includes predicates to assert disjointness of two maps (predicate
      [disjoint]), and coherence of two maps on the intersection of their
      domain (predicate [agree]).
    - It comes with a tactic for [fmap_eq] proving equalities modulo
      commutativity and associativity of map union.

    The definition of the type [fmap] is slightly technical in that it
    involves a dependent pair to pack the partial function of type
    [A -> option B] that represents the map, together with a proof of
    finiteness of the domain of this map. One useful lemma established
    in this file is the existence of fresh keys: for any finite map whose
    keys are natural numbers, there exists a natural number that does not
    already belong to the domain of that map. *)

(* ================================================================= *)
(** ** Representation of Potentially-Infinite Maps as Partial Functions *)

(* ----------------------------------------------------------------- *)
(** *** Representation *)

(** Type of partial functions from A to B *)

Definition map (A B : Type) : Type :=
  A -> option B.

(* ----------------------------------------------------------------- *)
(** *** Operations *)

(** Disjoint union of two partial functions *)

Definition map_union (A B : Type) (f1 f2 : map A B) : map A B :=
  fun (x:A) => match f1 x with
           | Some y => Some y
           | None => f2 x
           end.

Definition map_merge (A B : Type) (m : B -> B -> B) (f1 f2 : map A B) : map A B :=
  fun (x:A) => 
    match f1 x, f2 x with
    | Some x, Some y => Some (m x y)
    | Some x, None   => Some x 
    | None  , x      => x
    end.

(** Removal from a partial functions *)

Definition map_remove (A B : Type) (f : map A B) (k:A) : map A B :=
  fun (x:A) => If x = k then None else f x.

(** Finite domain of a partial function *)

Definition map_finite (A B : Type) (f : map A B) :=
  exists (L : list A), forall (x:A), f x <> None -> mem x L.

(** Disjointness of domain of two partial functions *)

Definition map_disjoint (A B : Type) (f1 f2 : map A B) :=
  forall (x:A), f1 x = None \/ f2 x = None.

(** Compatibility of two partial functions on the intersection
    of their domains (only for Separation Logic with RO-permissions) *)

Definition map_agree (A B : Type) (f1 f2 : map A B) :=
  forall x v1 v2,
  f1 x = Some v1 ->
  f2 x = Some v2 ->
  v1 = v2.

(** Domain of a map (as a predicate) *)

Definition map_indom (A B : Type) (f1 : map A B) : (A->Prop) :=
  fun (x:A) => f1 x <> None.

(** Filter the bindings of a map *)

Definition map_filter A B (F:A->B->Prop) (f:map A B) : map A B :=
  fun (x:A) => match f x with
    | None => None
    | Some y => If F x y then Some y else None
    end.

(** Map a function on the values of a map *)

Definition map_map A B1 B2 (F:A->B1->B2) (f:map A B1) : map A B2 :=
  fun (x:A) => match f x with
    | None => None
    | Some y => Some (F x y)
    end.

(* ----------------------------------------------------------------- *)
(** *** Properties *)

Section MapOps.
Variables (A B : Type).
Implicit Types f : map A B.

(** Disjointness and domains *)

Lemma map_disjoint_eq : forall f1 f2,
  map_disjoint f1 f2 = (forall x, map_indom f1 x -> map_indom f2 x -> False).
Proof using.
  intros. unfold map_disjoint, map_indom. extens. iff M.
  { intros x. specializes M x. gen M. case_eq (f1 x); case_eq (f2 x); auto_false*. }
  { intros x. specializes M x. gen M. case_eq (f1 x); case_eq (f2 x); auto_false*.
    { intros. false. applys M; auto_false. } }
Qed.

(** Symmetry of disjointness *)

Lemma map_disjoint_sym :
  sym (@map_disjoint A B).
Proof using.
  introv H. unfolds map_disjoint. intros z. specializes H z. intuition.
Qed.

(** Commutativity of disjoint union *)

Lemma map_union_comm : forall f1 f2,
  map_disjoint f1 f2 ->
  map_union f1 f2 = map_union f2 f1.
Proof using.
  introv H. unfold map.
  extens. intros x. unfolds map_disjoint, map_union.
  specializes H x. cases (f1 x); cases (f2 x); auto. destruct H; false.
Qed.

(** Finiteness of union *)

Lemma map_union_finite : forall f1 f2,
  map_finite f1 ->
  map_finite f2 ->
  map_finite (map_union f1 f2).
Proof using.
  introv [L1 F1] [L2 F2]. exists (L1 ++ L2). intros x M.
  specializes F1 x. specializes F2 x. unfold map_union in M.
  apply mem_app. destruct~ (f1 x).
Qed.

Lemma map_merge_finite m : forall f1 f2,
  map_finite f1 ->
  map_finite f2 ->
  map_finite (map_merge m f1 f2).
Proof using.
  introv [L1 F1] [L2 F2]. exists (L1 ++ L2). intros x M.
  specializes F1 x. specializes F2 x. unfold map_merge in M.
  apply mem_app; destruct (f1 x), (f2 x); try by ((left; apply F1)+(right;apply F2)).
Qed.


(** Finiteness of removal *)

Definition map_remove_finite : forall x f,
  map_finite f ->
  map_finite (map_remove f x).
Proof using.
  introv [L F]. exists L. intros x' M.
  specializes F x'. unfold map_remove in M. case_if~.
Qed.

(** Finiteness of filter *)

Definition map_filter_finite : forall (F:A->B->Prop) f,
  map_finite f ->
  map_finite (map_filter F f).
Proof using.
  introv [L N]. exists L. intros x' M.
  specializes N x'. unfold map_filter in M.
  destruct (f x'); tryfalse. case_if. applys N; auto_false.
Qed.

(** Finiteness of map *)

Definition map_map_finite : forall C (F:A->B->C) f,
  map_finite f ->
  map_finite (map_map F f).
Proof using.
  introv [L N]. exists L. intros x' M.
  specializes N x'. unfold map_map in M.
  destruct (f x'); tryfalse. applys N; auto_false.
Qed.

End MapOps.

(* ================================================================= *)
(** ** Representation of Finite Maps as Dependent Pairs *)

(* ----------------------------------------------------------------- *)
(** *** Representation *)

Unset Elimination Schemes.

Inductive fmap (A B : Type) : Type := make {
  fmap_data :> map A B;
  fmap_finite : map_finite fmap_data }.

Set Elimination Schemes.

Definition fset A := fmap A unit.

Arguments make [A] [B].

(* ----------------------------------------------------------------- *)
(** *** Operations *)

Declare Scope fmap_scope.

(** Domain of a fmap (as a predicate) *)

Definition indom (A B: Type) (h:fmap A B) : (A->Prop) :=
  map_indom h.

(** Empty fmap *)

Program Definition empty (A B : Type) : fmap A B :=
  make (fun l => None) _.
Next Obligation. exists (@nil A). auto_false. Qed.

Arguments empty {A} {B}.

(** Singleton fmap *)

Program Definition single A B (x:A) (v:B) : fmap A B :=
  make (fun x' => If x = x' then Some v else None) _.
Next Obligation.
  exists (x::nil). intros. case_if. subst~.
Qed.

(** Union of fmaps *)

Program Definition union A B (h1 h2:fmap A B) : fmap A B :=
  make (map_union h1 h2) _.
Next Obligation. destruct h1. destruct h2. apply~ map_union_finite. Qed.

Program Definition merge A B m (h1 h2:fmap A B) : fmap A B :=
  make (map_merge m h1 h2) _.
Next Obligation. destruct h1. destruct h2. apply~ map_merge_finite. Qed.


Notation "h1 \+ h2" := (union h1 h2)
   (at level 51, right associativity) : fmap_scope.

Notation "h1 '\[[' m ']]' h2" := (merge m h1 h2)
   (at level 51, right associativity, format "h1  \[[ m ]]  h2") : fmap_scope.


Open Scope fmap_scope.

(** Update of a fmap *)

Definition update A B (h:fmap A B) (x:A) (v:B) : fmap A B :=
  union (single x v) h.
  (* Note: the union operation first reads in the first argument. *)

(** Read in a fmap *)

Definition read (A B : Type) {IB:Inhab B} (h:fmap A B) (x:A) : B :=
  match fmap_data h x with
  | Some y => y
  | None => arbitrary
  end.

(** Removal from a fmap *)

Program Definition remove A B (h:fmap A B) (x:A) : fmap A B :=
  make (map_remove h x) _.
Next Obligation. destruct h. apply~ map_remove_finite. Qed.

(** Filter from a fmap *)

Program Definition filter A B (F:A->B->Prop) (h:fmap A B) : fmap A B :=
  make (map_filter F h) _.
Next Obligation. destruct h. apply~ map_filter_finite. Qed.

(** Map a function onto the keys of a fmap *)

Program Definition map_ A B1 B2 (F:A->B1->B2) (h:fmap A B1) : fmap A B2 :=
  make (map_map F h) _.
Next Obligation. destruct h. apply~ map_map_finite. Qed.

(** Inhabited type [fmap] *)

Global Instance Inhab_fmap A B : Inhab (fmap A B).
Proof using. intros. applys Inhab_of_val (@empty A B). Qed.

(* ================================================================= *)
(** ** Predicates on Finite Maps *)

(** Compatible fmaps (only for Separation Logic with RO-permissions) *)

Definition agree A B (h1 h2:fmap A B) :=
  map_agree h1 h2.

(** Disjoint fmaps *)

Definition disjoint A B (h1 h2 : fmap A B) : Prop :=
  map_disjoint h1 h2.

(** Three disjoint fmaps (not needed for basic separation logic) *)

Definition disjoint_3 A B (h1 h2 h3 : fmap A B) :=
     disjoint h1 h2
  /\ disjoint h2 h3
  /\ disjoint h1 h3.

(** Notation for disjointness *)

Module NotationForFmapDisjoint.

Notation "\# h1 h2" := (disjoint h1 h2)
  (at level 40, h1 at level 0, h2 at level 0, no associativity) : fmap_scope.

Notation "\# h1 h2 h3" := (disjoint_3 h1 h2 h3)
  (at level 40, h1 at level 0, h2 at level 0, h3 at level 0, no associativity)
  : fmap_scope.

End NotationForFmapDisjoint.

Import NotationForFmapDisjoint.

(* ################################################################# *)
(** * Poperties of Operations on Finite Maps *)

Section FmapProp.
Variables (A B : Type).
Implicit Types f g h : fmap A B.
Implicit Types x : A.
Implicit Types v : B.

(* ================================================================= *)
(** ** Equality *)

Lemma make_eq : forall (f1 f2:map A B) F1 F2,
  (forall x, f1 x = f2 x) ->
  make f1 F1 = make f2 F2.
Proof using.
  introv H. asserts: (f1 = f2). { unfold map. extens~. }
  subst. fequals. (* note: involves proof irrelevance *)
Qed.

Lemma eq_inv_fmap_data_eq : forall h1 h2,
  h1 = h2 ->
  forall x, fmap_data h1 x = fmap_data h2 x.
Proof using. intros. fequals. Qed.

Lemma fmap_extens : forall h1 h2,
  (forall x, fmap_data h1 x = fmap_data h2 x) ->
  h1 = h2.
Proof using. intros [f1 F1] [f2 F2] M. simpls. applys~ make_eq. Qed.


(* ================================================================= *)
(** ** Domain *)

Lemma indom_single_eq : forall x y v,
  indom (single x v) y = (x = y).
Proof using.
  intros. unfold single, indom, map_indom. simpl. extens. case_if; auto_false.
Qed.

Lemma indom_single : forall x v,
  indom (single x v) x.
Proof using. intros. rewrite* indom_single_eq. Qed.

Lemma indom_union_eq : forall h1 h2 x,
  indom (union h1 h2) x = (indom h1 x \/ indom h2 x).
Proof using.
  intros. extens. unfolds indom, union, map_indom, map_union. simpls.
  case_eq (fmap_data h1 x); case_eq (fmap_data h2 x); auto_false*.
Qed.

Lemma indom_merge_eq : forall m h1 h2 x,
  indom (h1 \[[m]] h2) x = (indom h1 x \/ indom h2 x).
Proof using.
  intros. extens. unfolds indom, merge, map_indom, map_merge. simpls.
  case_eq (fmap_data h1 x); case_eq (fmap_data h2 x); auto_false*.
  split=> //; by left.
Qed.

Lemma indom_union_l : forall h1 h2 x,
  indom h1 x ->
  indom (union h1 h2) x.
Proof using. intros. rewrite* indom_union_eq. Qed.

Lemma indom_union_r : forall h1 h2 x,
  indom h2 x ->
  indom (union h1 h2) x.
Proof using. intros. rewrite* indom_union_eq. Qed.

Lemma indom_merge_l m : forall h1 h2 x,
  indom h1 x ->
  indom (merge m h1 h2) x.
Proof using. intros. rewrite* indom_merge_eq. Qed.

Lemma indom_merge_r m : forall h1 h2 x,
  indom h2 x ->
  indom (merge m h1 h2) x.
Proof using. intros. rewrite* indom_merge_eq. Qed.


Lemma indom_update_eq : forall h x v y,
  indom (update h x v) y = (x = y \/ indom h y).
Proof using.
  intros. unfold update. rewrite indom_union_eq indom_single_eq. auto.
Qed.

Lemma indom_remove_eq : forall h x y,
  indom (remove h x) y = (x <> y /\ indom h y).
Proof using.
  intros. extens. unfolds indom, remove, map_indom, map_remove. simpls.
  case_if; auto_false*.
Qed.

(* ================================================================= *)
(** ** Disjoint and Domain *)

Lemma disjoint_eq : forall h1 h2,
  disjoint h1 h2 = (forall x, indom h1 x -> indom h2 x -> False).
Proof using. intros [f1 F1] [f2 F2]. apply map_disjoint_eq. Qed.

Lemma disjoint_eq' : forall h1 h2,
  disjoint h1 h2 = (forall x, indom h1 x -> indom h2 x -> False).
Proof using.
  extens. iff D E.
  { introv M1 M2. destruct (D x); false*. }
  { intros x. specializes E x. unfolds indom, map_indom.
    applys not_not_inv. intros N. rew_logic in N. false*. }
Qed. 
Lemma disjoint_of_not_indom_both : forall h1 h2,
  (forall x, indom h1 x -> indom h2 x -> False) ->
  disjoint h1 h2.
Proof using. introv M. rewrite~ disjoint_eq. Qed.

Lemma disjoint_inv_not_indom_both : forall h1 h2 x,
  disjoint h1 h2 ->
  indom h1 x ->
  indom h2 x ->
  False.
Proof using. introv. rewrite* disjoint_eq. Qed.

Lemma disjoint_single_of_not_indom : forall h x v,
  ~ indom h x ->
  disjoint (single x v) h.
Proof using.
  introv N. unfolds disjoint, map_disjoint. unfolds single, indom, map_indom.
  simpl. rew_logic in N. intros l'. case_if; subst; autos*.
Qed.

(** Note that the reciprocal of the above lemma is a special instance of
   [disjoint_inv_not_indom_both] *)

(* ================================================================= *)
(** ** Disjointness *)

Lemma disjoint_sym : forall h1 h2,
  \# h1 h2 ->
  \# h2 h1.
Proof using. intros [f1 F1] [f2 F2]. apply map_disjoint_sym. Qed.

Lemma disjoint_comm : forall h1 h2,
  \# h1 h2 = \# h2 h1.
Proof using. lets: disjoint_sym. extens*. Qed.

Lemma disjoint_empty_l : forall h,
  \# empty h.
Proof using. intros [f F] x. simple~. Qed.

Lemma disjoint_empty_r : forall h,
  \# h empty.
Proof using. intros [f F] x. simple~. Qed.

Hint Immediate disjoint_sym.
Hint Resolve disjoint_empty_l disjoint_empty_r.

Lemma disjoint_union_eq_r : forall h1 h2 h3,
  \# h1 (h2 \+ h3) =
  (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros [f1 F1] [f2 F2] [f3 F3].
  unfolds disjoint, union. simpls.
  unfolds map_disjoint, map_union. extens. iff M [M1 M2].
  split; intros x; specializes M x;
   destruct (f2 x); intuition; tryfalse.
  intros x. specializes M1 x. specializes M2 x.
   destruct (f2 x); intuition.
Qed.

Lemma disjoint_merge_eq_r m : forall h1 h2 h3,
  \# h1 (h2 \[[m]] h3) =
  (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros [f1 F1] [f2 F2] [f3 F3].
  unfolds disjoint, merge. simpls.
  unfolds map_disjoint, map_merge. extens. iff M [M1 M2].
  split; intros x; specializes M x;
   destruct (f1 x), (f2 x), (f3 x); intuition; tryfalse.
  intros x. specializes M1 x. specializes M2 x.
   destruct (f2 x); intuition; by [].
Qed.

Lemma disjoint_union_eq_l : forall h1 h2 h3,
  \# (h2 \+ h3) h1 =
  (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros. rewrite disjoint_comm.
  apply disjoint_union_eq_r.
Qed.

Lemma disjoint_merge_eq_l m : forall h1 h2 h3,
  \# (h2 \[[m]] h3) h1 =
  (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros. rewrite disjoint_comm.
  apply disjoint_merge_eq_r.
Qed.


Lemma disjoint_single_single : forall (x1 x2:A) (v1 v2:B),
  x1 <> x2 ->
  \# (single x1 v1) (single x2 v2).
Proof using.
  introv N. intros x. simpls. do 2 case_if; auto.
Qed.

Lemma disjoint_single_single_same_inv : forall (x:A) (v1 v2:B),
  \# (single x v1) (single x v2) ->
  False.
Proof using.
  introv D. specializes D x. simpls. case_if. destruct D; tryfalse.
Qed.

Lemma disjoint_3_unfold : forall h1 h2 h3,
  \# h1 h2 h3 = (\# h1 h2 /\ \# h2 h3 /\ \# h1 h3).
Proof using. auto. Qed.

Lemma disjoint_single_set : forall h l v1 v2,
  \# (single l v1) h ->
  \# (single l v2) h.
Proof using.
  introv M. unfolds disjoint, single, map_disjoint; simpls.
  intros l'. specializes M l'. case_if~. destruct M; auto_false.
Qed.

Lemma disjoint_update_l : forall h1 h2 x v,
  disjoint h1 h2 ->
  indom h1 x ->
  disjoint (update h1 x v) h2.
Proof using.
  introv HD Hx. rewrite ?disjoint_eq in HD *. intros y Hy1 Hy2.
  rewrite indom_update_eq in Hy1. destruct Hy1.
  { subst. false*. }
  { applys* HD y. }
Qed.

Lemma disjoint_update_not_r : forall h1 h2 x v,
  disjoint h1 h2 ->
  ~ indom h2 x ->
  disjoint (update h1 x v) h2.
Proof using.
  introv HD Hx. rewrite ?disjoint_eq in HD *. intros y Hy1 Hy2.
  rewrite indom_update_eq in Hy1. destruct Hy1.
  { subst. false*. }
  { applys* HD y. }
Qed. 
Lemma disjoint_remove_l : forall h1 h2 x,
  disjoint h1 h2 ->
  disjoint (remove h1 x) h2.
Proof using.
  introv M. rewrite ?disjoint_eq in M *. intros y Hy1 Hy2.
  rewrite* indom_remove_eq in Hy1.
Qed.

(* ================================================================= *)
(** ** Union *)

Lemma union_self : forall h,
  h \+ h = h.
Proof using.
  intros [f F]. apply~ make_eq. simpl. intros x.
  unfold map_union. cases~ (f x).
Qed.

Lemma union_empty_l : forall h,
  empty \+ h = h.
Proof using.
  intros [f F]. unfold union, map_union, empty. simpl.
  apply~ make_eq.
Qed.

Lemma merge_empty_l m : forall h,
  empty \[[m]] h = h.
Proof using.
  intros [f F]. unfold merge, map_merge, empty. simpl.
  apply~ make_eq.
Qed.


Lemma merge_empty_r m : forall h,
  h \[[m]] empty = h.
Proof using.
  intros [f F]. unfold merge, map_merge, empty. simpl.
  apply make_eq. intros x. destruct~ (f x).
Qed.

Lemma union_empty_r : forall h,
  h \+ empty = h.
Proof using.
  intros [f F]. unfold union, map_union, empty. simpl.
  apply make_eq. intros x. destruct~ (f x).
Qed.


Lemma union_eq_empty_inv_l : forall h1 h2,
  h1 \+ h2 = empty ->
  h1 = empty.
Proof using.
  intros (f1&F1) (f2&F2) M. inverts M as M.
  applys make_eq. intros l.
  unfolds map_union.
  lets: fun_eq_1 l M.
  cases (f1 l); auto_false.
Qed.

Lemma union_eq_empty_inv_r : forall h1 h2,
  h1 \+ h2 = empty ->
  h2 = empty.
Proof using.
  intros (f1&F1) (f2&F2) M. inverts M as M.
  applys make_eq. intros l.
  unfolds map_union.
  lets: fun_eq_1 l M.
  cases (f1 l); auto_false.
Qed.

Lemma union_comm_of_disjoint : forall h1 h2,
  \# h1 h2 ->
  h1 \+ h2 = h2 \+ h1.
Proof using.
  intros [f1 F1] [f2 F2] H. simpls. apply make_eq. simpl.
  intros. rewrite~ map_union_comm.
Qed.

Lemma union_comm_of_agree : forall h1 h2,
  agree h1 h2 ->
  h1 \+ h2 = h2 \+ h1.
Proof using.
  intros [f1 F1] [f2 F2] H. simpls. apply make_eq. simpl.
  intros l. specializes H l. unfolds map_union. simpls.
  cases (f1 l); cases (f2 l); auto. fequals. applys* H.
Qed.

Lemma merge_comm m : forall h1 h2,
  (forall a b, m a b = m b a) ->
  h1 \[[m]] h2 = h2 \[[m]] h1.
Proof using.
  intros [f1 F1] [f2 F2] H. simpls. apply make_eq. simpl.
  intros l. unfolds map_merge. simpls.
  cases (f1 l); cases (f2 l); auto. fequals.
Qed.

Lemma union_assoc : forall h1 h2 h3,
  (h1 \+ h2) \+ h3 = h1 \+ (h2 \+ h3).
Proof using.
  intros [f1 F1] [f2 F2] [f3 F3]. unfolds union. simpls.
  apply make_eq. intros x. unfold map_union. destruct~ (f1 x).
Qed.

Lemma merge_assoc m : forall h1 h2 h3,
  (forall a b c, m a (m b c) = m (m a b) c) ->
  (h1 \[[m]] h2) \[[m]] h3 = h1 \[[m]] (h2 \[[m]] h3).
Proof using.
  intros [f1 F1] [f2 F2] [f3 F3]. unfolds merge. simpls=> E.
  apply make_eq. intros x. unfold map_merge. 
  destruct (f3 x), (f2 x), (f1 x); autos*; fequals.
Qed.


Lemma union_eq_inv_of_disjoint : forall h2 h1 h1',
  \# h1 h2 ->
  \# h1' h2 ->
  h1 \+ h2 = h1' \+ h2 ->
  h1 = h1'.
Proof using.
  intros [f2 F2] [f1' F1'] [f1 F1] D D' E.
  applys make_eq. intros x. specializes D x. specializes D' x.
  lets E': eq_inv_fmap_data_eq (rm E) x. simpls.
  unfolds map_union.
  cases (f1' x); cases (f1 x);
    destruct D; try congruence;
    destruct D'; try congruence.
Qed.

(* ================================================================= *)
(** ** Compatibility *)

Lemma agree_refl : forall h,
  agree h h.
Proof using.
  intros h. introv M1 M2. congruence.
Qed.

Lemma agree_sym : forall f1 f2,
  agree f1 f2 ->
  agree f2 f1.
Proof using.
  introv M. intros l v1 v2 E1 E2.
  specializes M l E1.
Qed.

Lemma agree_of_disjoint : forall h1 h2,
  disjoint h1 h2 ->
  agree h1 h2.
Proof using.
  introv HD. intros l v1 v2 M1 M2. destruct (HD l); false.
Qed.

Lemma agree_empty_l : forall h,
  agree empty h.
Proof using. intros h l v1 v2 E1 E2. simpls. false. Qed.

Lemma agree_empty_r : forall h,
  agree h empty.
Proof using.
  hint agree_sym, agree_empty_l. eauto.
Qed.

Lemma agree_union_l : forall f1 f2 f3,
  agree f1 f3 ->
  agree f2 f3 ->
  agree (f1 \+ f2) f3.
Proof using.
  introv M1 M2. intros l v1 v2 E1 E2.
  specializes M1 l. specializes M2 l.
  simpls. unfolds map_union. cases (fmap_data f1 l).
  { inverts E1. applys* M1. }
  { applys* M2. }
Qed.

Lemma agree_union_r : forall f1 f2 f3,
  agree f1 f2 ->
  agree f1 f3 ->
  agree f1 (f2 \+ f3).
Proof using.
  hint agree_sym, agree_union_l. eauto.
Qed.

Lemma agree_union_lr : forall f1 g1 f2 g2,
  agree g1 g2 ->
  \# f1 f2 (g1 \+ g2) ->
  agree (f1 \+ g1) (f2 \+ g2).
Proof using.
  introv M1 (M2a&M2b&M2c).
  rewrite ?disjoint_union_eq_r in M1, M2a, M2b, M2c.
  applys agree_union_l; applys agree_union_r;
    try solve [ applys* agree_of_disjoint ].
  auto.
Qed.

Lemma agree_union_ll_inv : forall f1 f2 f3,
  agree (f1 \+ f2) f3 ->
  agree f1 f3.
Proof using.
  introv M. intros l v1 v2 E1 E2.
  specializes M l. simpls. unfolds map_union.
  rewrite E1 in M. applys* M.
Qed.

Lemma agree_union_rl_inv : forall f1 f2 f3,
  agree f1 (f2 \+ f3) ->
  agree f1 f2.
Proof using.
  hint agree_union_ll_inv, agree_sym. eauto.
Qed.

Lemma agree_union_lr_inv_agree_agree : forall f1 f2 f3,
  agree (f1 \+ f2) f3 ->
  agree f1 f2 ->
  agree f2 f3.
Proof using.
  introv M D. rewrite~ (@union_comm_of_agree f1 f2) in M.
  applys* agree_union_ll_inv.
Qed.

Lemma agree_union_rr_inv_agree : forall f1 f2 f3,
  agree f1 (f2 \+ f3) ->
  agree f2 f3 ->
  agree f1 f3.
Proof using.
  hint agree_union_lr_inv_agree_agree, agree_sym. eauto.
Qed.

Lemma agree_union_l_inv : forall f1 f2 f3,
  agree (f1 \+ f2) f3 ->
  agree f1 f2 ->
     agree f1 f3
  /\ agree f2 f3.
Proof using.
  introv M1 M2. split.
  { applys* agree_union_ll_inv. }
  { applys* agree_union_lr_inv_agree_agree. }
Qed.

Lemma agree_union_r_inv : forall f1 f2 f3,
  agree f1 (f2 \+ f3) ->
  agree f2 f3 ->
     agree f1 f2
  /\ agree f1 f3.
Proof using.
  hint agree_sym.
  intros. forwards~ (M1&M2): agree_union_l_inv f2 f3 f1.
Qed.

(* ================================================================= *)
(** ** Read *)

Lemma read_single : forall {IB:Inhab B} x v,
  read (single x v) x = v.
Proof using.
  intros. unfold read, single. simpl. case_if~.
Qed.

Lemma read_union_l : forall {IB:Inhab B} h1 h2 x,
  indom h1 x ->
  read (union h1 h2) x = read h1 x.
Proof using.
  intros. unfold read, union, map_union. simpl.
  case_eq (fmap_data h1 x); auto_false.
Qed.

Lemma read_union_r : forall {IB:Inhab B} h1 h2 x,
  ~ indom h1 x ->
  read (union h1 h2) x = read h2 x.
Proof using.
  intros. unfold read, union, map_union. simpl.
  case_eq (fmap_data h1 x).
  { intros v Hv. false H. auto_false. }
  { auto_false. }
Qed.

(* ================================================================= *)
(** ** Update *)

Lemma update_eq_union_single : forall h x v,
  update h x v = union (single x v) h.
Proof using. auto. Qed.

Lemma update_single : forall x v w,
  update (single x v) x w = single x w.
Proof using.
  intros. rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, single. simpl. case_if~.
Qed.

Lemma update_union_l : forall h1 h2 x v,
  indom h1 x ->
  update (union h1 h2) x v = union (update h1 x v) h2.
Proof using.
  intros. do 2 rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, union, map_union. simpl. case_if~.
Qed.

Lemma update_union_r : forall h1 h2 x v,
  ~ indom h1 x ->
  update (union h1 h2) x v = union h1 (update h2 x v).
Proof using.
  introv M. asserts IB: (Inhab B). { applys Inhab_of_val v. }
  do 2 rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, union, map_union. simpl. case_if~.
  { subst. case_eq (fmap_data h1 y); auto_false.
    { intros w Hw. false M. auto_false. } }
Qed.

Lemma update_union_not_r : forall h1 h2 x v,
  ~ indom h2 x ->
  update (union h1 h2) x v = union (update h1 x v) h2.
Proof using.
  intros. do 2 rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, union, map_union. simpl. case_if~.
Qed.

Lemma update_union_not_l : forall h1 h2 x v,
  ~ indom h1 x ->
  update (union h1 h2) x v = union h1 (update h2 x v).
Proof using.
  introv M. asserts IB: (Inhab B). { applys Inhab_of_val v. }
  do 2 rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, union, map_union. simpl. case_if~.
  { subst. case_eq (fmap_data h1 y); auto_false.
    { intros w Hw. false M. auto_false. } }
Qed. 

(* ================================================================= *)
(** ** Removal *)

Lemma remove_disjoint_union_l : forall h1 h2 x,
  indom h1 x ->
  disjoint h1 h2 ->
  remove (union h1 h2) x = union (remove h1 x) h2.
Proof using.
  introv M D. applys fmap_extens. intros y.
  rewrite disjoint_eq in D. specializes D M. asserts* D': (~ indom h2 x).
  unfold remove, map_remove, union, map_union, single. simpls. case_if.
  { destruct h1 as [f1 F1]. unfolds indom, map_indom. simpls. subst.
    rew_logic~ in D'. }
  { auto. }
Qed.

Lemma remove_union_single_l : forall h x v,
  ~ indom h x ->
  remove (union (single x v) h) x = h.
Proof using.
  introv M. applys fmap_extens. intros y.
  unfold remove, map_remove, union, map_union, single. simpls. case_if.
  { destruct h as [f F]. unfolds indom, map_indom. simpls. subst. rew_logic~ in M. }
  { case_if~. }
Qed.

End FmapProp.

(** Fixing arguments *)

Arguments union_assoc [A] [B].
Arguments union_comm_of_disjoint [A] [B].
Arguments union_comm_of_agree [A] [B].

(* ################################################################# *)
(** * Tactics for Finite Maps *)

(* ================================================================= *)
(** ** Tactic [disjoint] for proving disjointness results *)

(** [disjoint] proves goals of the form [\# h1 h2] and
    [\# h1 h2 h3] by expanding all hypotheses into binary forms
    [\# h1 h2] and then exploiting symmetry and disjointness
    with [empty]. *)

Module Export DisjointHints.
Hint Resolve disjoint_sym disjoint_empty_l disjoint_empty_r.
End DisjointHints.

Hint Rewrite
  disjoint_union_eq_l
  disjoint_union_eq_r
  disjoint_3_unfold : rew_disjoint.

Tactic Notation "rew_disjoint" :=
  autorewrite with rew_disjoint in *.
Tactic Notation "rew_disjoint" "*" :=
  rew_disjoint; auto_star.

Ltac fmap_disjoint_pre tt :=
  subst; rew_disjoint; jauto_set.

Tactic Notation "fmap_disjoint" :=
  solve [ fmap_disjoint_pre tt; auto ].

Lemma disjoint_demo : forall A B (h1 h2 h3 h4 h5:fmap A B),
  h1 = h2 \+ h3 ->
  \# h2 h3 ->
  \# h1 h4 h5 ->
  \# h3 h2 h5 /\ \# h4 h5.
Proof using.
  intros. dup 2.
  { subst. rew_disjoint. jauto_set. auto. auto. auto. auto. }
  { fmap_disjoint. }
Qed.

(* ================================================================= *)
(** ** Tactic [rew_map] for Normalizing Expressions *)

Hint Rewrite
  union_assoc
  union_empty_l
  union_empty_r : rew_fmap rew_fmap_for_fmap_eq.

Tactic Notation "rew_fmap" :=
  autorewrite with rew_fmap in *.

Tactic Notation "rew_fmap" "~" :=
  rew_fmap; auto_tilde.

Tactic Notation "rew_fmap" "*" :=
  rew_fmap; auto_star.

(* ================================================================= *)
(** ** Tactic [fmap_eq] for Proving Equalities *)

Section StateEq.
Variables (A B : Type).
Implicit Types h : fmap A B.

(** [eq] proves equalities between unions of fmaps, of the form
    [h1 \+ h2 \+ h3 \+ h4 = h1' \+ h2' \+ h3' \+ h4']
    It attempts to discharge the disjointness side-conditions.
    Disclaimer: it cancels heaps at depth up to 4, but no more. *)

Lemma union_eq_cancel_1 : forall h1 h2 h2',
  h2 = h2' ->
  h1 \+ h2 = h1 \+ h2'.
Proof using. intros. subst. auto. Qed.

Lemma union_eq_cancel_1' : forall h1,
  h1 = h1.
Proof using. intros. auto. Qed.

Lemma union_eq_cancel_2 : forall h1 h1' h2 h2',
  \# h1 h1' ->
  h2 = h1' \+ h2' ->
  h1 \+ h2 = h1' \+ h1 \+ h2'.
Proof using.
  intros. subst. rewrite <- union_assoc.
  rewrite (union_comm_of_disjoint h1 h1').
  rewrite~ union_assoc. auto.
Qed.

Lemma union_eq_cancel_2' : forall h1 h1' h2,
  \# h1 h1' ->
  h2 = h1' ->
  h1 \+ h2 = h1' \+ h1.
Proof using.
  intros. subst. apply~ union_comm_of_disjoint.
Qed.

Lemma union_eq_cancel_3 : forall h1 h1' h2 h2' h3',
  \# h1 (h1' \+ h2') ->
  h2 = h1' \+ h2' \+ h3' ->
  h1 \+ h2 = h1' \+ h2' \+ h1 \+ h3'.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h1' h2' h3').
  rewrite <- (union_assoc h1' h2' (h1 \+ h3')).
  apply~ union_eq_cancel_2.
Qed.

Lemma union_eq_cancel_3' : forall h1 h1' h2 h2',
  \# h1 (h1' \+ h2') ->
  h2 = h1' \+ h2' ->
  h1 \+ h2 = h1' \+ h2' \+ h1.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h1' h2' h1).
  apply~ union_eq_cancel_2'.
Qed.

Lemma union_eq_cancel_4 : forall h1 h1' h2 h2' h3' h4',
  \# h1 ((h1' \+ h2') \+ h3') ->
  h2 = h1' \+ h2' \+ h3' \+ h4' ->
  h1 \+ h2 = h1' \+ h2' \+ h3' \+ h1 \+ h4'.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h1' h2' (h3' \+ h4')).
  rewrite <- (union_assoc h1' h2' (h3' \+ h1 \+ h4')).
  apply~ union_eq_cancel_3.
Qed.

Lemma union_eq_cancel_4' : forall h1 h1' h2 h2' h3',
  \# h1 (h1' \+ h2' \+ h3') ->
  h2 = h1' \+ h2' \+ h3' ->
  h1 \+ h2 = h1' \+ h2' \+ h3' \+ h1.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h2' h3' h1).
  apply~ union_eq_cancel_3'.
Qed.

End StateEq.

Ltac fmap_eq_step tt :=
  match goal with | |- ?G => match G with
  | ?h1 = ?h1 => apply union_eq_cancel_1'
  | ?h1 \+ ?h2 = ?h1 \+ ?h2' => apply union_eq_cancel_1
  | ?h1 \+ ?h2 = ?h1' \+ ?h1 => apply union_eq_cancel_2'
  | ?h1 \+ ?h2 = ?h1' \+ ?h1 \+ ?h2' => apply union_eq_cancel_2
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h1 => apply union_eq_cancel_3'
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h1 \+ ?h3' => apply union_eq_cancel_3
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h3' \+ ?h1 => apply union_eq_cancel_4'
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h3' \+ ?h1 \+ ?h4' => apply union_eq_cancel_4
  end end.

Tactic Notation "fmap_eq" :=
  subst;
  autorewrite with rew_fmap_for_fmap_eq;
  repeat (fmap_eq_step tt);
  try match goal with
  | |- \# _ _ => fmap_disjoint
  | |- \# _ _ _ => fmap_disjoint
  end.

Tactic Notation "fmap_eq" "~" :=
  fmap_eq; auto_tilde.

Tactic Notation "fmap_eq" "*" :=
  fmap_eq; auto_star.

Lemma fmap_eq_demo : forall A B (h1 h2 h3 h4 h5:fmap A B),
  \# h1 h2 h3 ->
  \# (h1 \+ h2 \+ h3) h4 h5 ->
  h1 = h2 \+ h3 ->
  h4 \+ h1 \+ h5 = h2 \+ h5 \+ h4 \+ h3.
Proof using.
  intros. dup 2.
  { subst. rew_fmap.
    fmap_eq_step tt. fmap_disjoint.
    fmap_eq_step tt.
    fmap_eq_step tt. fmap_disjoint. auto. }
  { fmap_eq. }
Qed.

(* ################################################################# *)
(** * Existence of Fresh Locations *)

(* ================================================================= *)
(** ** Consecutive Locations *)

(** The notion of "consecutive locations" is useful for reasoning about
    records and arrays. *)

Fixpoint conseq (B:Type) (vs:list B) (l:nat) : fmap nat B :=
  match vs with
  | nil => empty
  | v::vs' => (single l v) \+ (conseq vs' (S l))
  end.

Lemma conseq_nil : forall B (l:nat),
  conseq (@nil B) l = empty.
Proof using. auto. Qed.

Lemma conseq_cons : forall B (l:nat) (v:B) (vs:list B),
  conseq (v::vs) l = (single l v) \+ (conseq vs (S l)).
Proof using. auto. Qed.

Lemma conseq_cons' : forall B (l:nat) (v:B) (vs:list B),
  conseq (v::vs) l = (single l v) \+ (conseq vs (l+1)).
Proof using. intros. math_rewrite (l+1 = S l)%nat. applys conseq_cons. Qed.

Global Opaque conseq.

Hint Rewrite conseq_nil conseq_cons : rew_listx.

(* ================================================================= *)
(** ** Existence of Fresh Locations *)

Definition loc_fresh_gen (L : list nat) :=
  (1 + fold_right plus O L)%nat.

Lemma loc_fresh_ind : forall l L,
  mem l L ->
  (l < loc_fresh_gen L)%nat.
Proof using.
  intros l L. unfold loc_fresh_gen.
  induction L; introv M; inverts M; rew_listx.
  { math. }
  { forwards~: IHL. math. }
Qed.

Lemma loc_fresh_nat_ge : forall (L:list nat),
  exists (l:nat), forall (i:nat), ~ mem (l+i)%nat L.
Proof using.
  intros L. exists (loc_fresh_gen L). intros i M.
  lets: loc_fresh_ind M. math.
Qed.

(** For any finite list of locations (implemented as [nat]), there exists
    one location not in that list. *)

Lemma loc_fresh_nat : forall (L:list nat),
  exists (l:nat), ~ mem l L.
Proof using.
  intros L. forwards (l&P): loc_fresh_nat_ge L.
  exists l. intros M. applys (P 0%nat). applys_eq M. math.
Qed.

Section FmapFresh.
Variables (B : Type).
Implicit Types h : fmap nat B.

(** For any heap, there exists one (non-null) location not already in the
    domain of that heap. *)

Lemma exists_fresh : forall null h,
  exists l, ~ indom h l /\ l <> null.
Proof using.
  intros null (m&(L&M)). unfold indom, map_indom. simpl.
  lets (l&F): (loc_fresh_nat (null::L)).
  exists l. split.
  { simpl. intros l'. forwards~ E: M l. }
  { intro_subst. applys~ F. }
Qed.

(** For any heap [h], there exists one (non-null) location [l] such that
    the singleton map that binds [l] to a value [v] is disjoint from [h]. *)

Lemma single_fresh : forall null h v,
  exists l, \# (single l v) h /\ l <> null.
Proof using.
  intros. forwards (l&F&N): exists_fresh null h.
  exists l. split~. applys* disjoint_single_of_not_indom.
Qed.

Lemma conseq_fresh : forall null h vs,
  exists l, \# (conseq vs l) h /\ l <> null.
Proof using.
  intros null (m&(L&M)) vs.
  unfold disjoint, map_disjoint. simpl.
  lets (l&F): (loc_fresh_nat_ge (null::L)).
  exists l. split.
  { intros l'. gen l. induction vs as [|v vs']; intros.
    { simple~. }
    { rewrite conseq_cons. destruct (IHvs' (S l)%nat) as [E|?].
      { intros i N. applys F (S i). applys_eq N. math. }
      { simpl. unfold map_union. case_if~.
        { subst. right. applys not_not_inv. intros H. applys F 0%nat.
          constructor. math_rewrite (l'+0 = l')%nat. applys~ M. } }
      { auto. } } }
  { intro_subst. applys~ F 0%nat. rew_nat. auto. }
Qed.

Lemma disjoint_single_conseq : forall B l l' L (v:B),
  (l < l')%nat \/ (l >= l'+length L)%nat ->
  \# (single l v) (conseq L l').
Proof using.
  introv N. gen l'. induction L as [|L']; intros.
  { rewrite~ conseq_nil. }
  { rew_list in N. rewrite conseq_cons. rew_disjoint. split.
    { applys disjoint_single_single. destruct N; math. }
    { applys IHL. destruct N. { left. math. } { right. math. } } }
Qed.

(* ================================================================= *)
(** ** Existence of a Smallest Fresh Locations *)

(** The notion of smallest fresh location is useful for setting up
    deterministic semantics. *)

Definition fresh (null:nat) (h:fmap nat B) (l:nat) : Prop :=
  ~ indom h l /\ l <> null.

Definition smallest_fresh (null:nat) (h:fmap nat B) (l:nat) : Prop :=
  fresh null h l /\ (forall l', l' < l -> ~ fresh null h l').

Lemma exists_smallest_fresh : forall null h,
  exists l, smallest_fresh null h l.
Proof using.
  intros.
  cuts M: (forall l0, fresh null h l0 ->
            exists l, fresh null h l
                   /\ (forall l', l' < l -> ~ fresh null h l')).
  { lets (l0&F&N): exists_fresh null h. applys M l0. split*. }
  intros l0. induction_wf IH: wf_lt l0. intros F.
  tests C: (forall l', l' < l0 -> ~ fresh null h l').
  { exists* l0. }
  { destruct C as (l0'&K). rew_logic in K. destruct K as (L&F').
    applys* IH l0'. }
Qed.

(* ================================================================= *)
(** ** Existence of Nonempty Heaps *)

(** The existence of nonempty (nat-indexed) finite maps is useful
    for constructing counterexamples. *)

Lemma exists_not_empty : forall `{IB:Inhab B},
  exists (h:fmap nat B), h <> empty.
Proof using.
  intros. sets l: 0%nat. sets h: (single l (arbitrary (A:=B))).
  exists h. intros N.
  sets h': (empty:fmap nat B).
  asserts M1: (indom h l).
  { applys indom_single. }
  asserts M2: (~ indom h' l).
  { unfolds @indom, map_indom, @empty. simpls. auto_false. }
  rewrite N in M1. false*.
Qed.

End FmapFresh.

Lemma remove_union_not_r  [A B : Type] [h1 h2 : fmap A B] [x : A] :
  ~ indom h2 x -> 
  remove h1 x \+ h2 = remove (h1 \+ h2) x.
Proof.
Admitted.

Lemma fmap_fold A B : forall P : Type,
  P -> 
  (A -> B -> P -> P) -> fmap A B -> P.
Proof.
Admitted.

Lemma fmap_foldE A B (P : Type) (p : P) (f : A -> B -> P -> P) :
  (fmap_fold p f empty = p) *
  ((forall (a b : A) (a' b' : B) (p : P), a <> b -> f a a' (f b b' p) = f b b' (f a a' p)) ->
    forall fm x y, ~ indom fm x -> fmap_fold p f (update fm x y) = f x y (fmap_fold p f fm)).
Admitted.

Lemma fmap_foldE' A B (P : Type) (p : P) (f : A -> B -> P -> P) :
  (fmap_fold p f empty = p) *
  ((forall (a b : A) (a' b' : B) (p : P), a <> b -> f a a' (f b b' p) = f b b' (f a a' p)) ->
   (forall x (y : B) y' y (p : P), f x y (f x y' p) = f x y p) ->
    forall fm x y, fmap_fold p f (update fm x y) = f x y (fmap_fold p f fm)).
Admitted.

(* Lemma fmap_foldE' A B (P : Type) (p : P) (f : A -> B -> P -> P) :
  (fmap_fold p f empty = p) *
  ( forall fm x y, fmap_fold p f (update fm x y) = f x y (fmap_fold p f fm)).
Admitted. *)


Lemma fset_fold A : forall P : Type,
  P -> 
  (A -> P -> P) -> fset A -> P.
Proof.
Admitted.

Lemma fset_foldE A (P : Type) (p : P) (f : A -> P -> P) :
  (fset_fold p f empty = p) *
  ((forall (a b : A) (p : P), f a (f b p) = f b (f a p)) ->
    forall fs x, ~ indom fs x -> fset_fold p f (update fs x tt) = f x (fset_fold p f fs)).
Admitted.

Lemma disjoint_update {A B} x y (fm1 fm2 : fmap A B) : 
  disjoint (update fm1 x y) fm2 = (~ indom fm2 x /\ disjoint fm1 fm2).
Proof.
Admitted.

Lemma fmap_ind A B : forall P : fmap A B -> Prop,
  P empty -> 
  (forall fs x y, P fs -> ~ indom fs x -> P (update fs x y)) -> forall fs, P fs.
Proof.
Admitted.


Lemma fset_ind A : forall P : fset A -> Prop,
  P empty -> 
  (forall fs x, P fs -> ~ indom fs x -> P (update fs x tt)) -> forall fs, P fs.
Proof.
Admitted.

Lemma fold_fset_eq {A P : Type} (fs : fset A) (f1 f2 : A -> P -> P) (p : P):
  (forall d, indom fs d -> f1 d = f2 d) ->
  fset_fold p f1 fs = fset_fold p f2 fs.
Admitted.

Lemma update_empty {A B : Type} {x : A} {y : B} :
  single x y = update empty x y.
Admitted.

Lemma update_update {A B : Type} {x z : A} {y w : B} (fm : fmap A B) :
  x <> z ->
    update (update fm x y) z w = 
    update (update fm z w) x y.
Proof.
Admitted.

Lemma update_updatexx {A B : Type} {x : A} {y w : B} (fm : fmap A B) :
    update (update fm x y) x w = 
    update fm x w.
Proof.
Admitted.

Search sig.

Definition map_fsubst {A B C : Type} (fm : map A B) (f : A -> C) : map C B :=
  fun c =>
    match classicT (exists a, f a = c /\ map_indom fm a) with
    | left P => match indefinite_description P with (exist a _) => fm a end
    | _ => None
    end.

Program Definition fsubst {A B C : Type} (fm : fmap A B) (f : A -> C) : fmap C B := 
  make (map_fsubst fm f) _.
Next Obligation. Admitted.

(* Definition valid_subst {A B C : Type} (fm : fmap A B) (f : A -> C) : Prop :=
  forall x1 x2, 
    indom fm x1 ->
    indom fm x2 ->
    f x1 = f x2 -> fmap_data fm x1 = fmap_data fm x2. *)

Definition valid_subst {A B C : Type} (fm : fmap A B) (f : A -> C) : Prop :=
  forall x1 x2, 
    f x1 = f x2 -> 
    fmap_data fm x1 = fmap_data fm x2.

Lemma valid_subst_union_l {A B C : Type} (fm1 fm2 : fmap A B) (f : A -> C) :
  valid_subst fm1 f ->
  disjoint fm1 fm2 ->
  valid_subst (fm1 \+ fm2) f ->
    valid_subst fm2 f.
Proof.
  move=> v1 dj v12 x1 x2 /[dup]/[dup] /v12/[swap]/v1.
  rewrite /union /= /map_union=> /[dup]+->.
  case: (dj x2)=> [->|] // .
  by case: (dj x1)=> [->?<-|-> ->].
Qed.

Lemma fsubst_valid_eq {A B C : Type} (f : A -> C) (fm : fmap A B) (x : A) :
  valid_subst fm f -> 
    fmap_data (fsubst fm f) (f x) = fmap_data fm x.
Proof.
  move=> v.
  rewrite /fsubst /= /map_fsubst.
  case: classicT=> pf.
  { case: (indefinite_description _); clear pf.
    by move=> ? [/v]. }
  case: (prop_inv (indom fm x))=> [?|/not_not_inv->] //.
  case: pf; by exists x.
Qed.



Lemma valid_subst_update {A B C : Type} (fm : fmap A B) (f : A -> C) x y : 
  valid_subst (update fm x y) f -> valid_subst fm f.
Proof.
Admitted.

Lemma valid_subst_filter {A B C : Type} (fm : fmap A B) (f : A -> C) Q : 
  valid_subst fm f -> valid_subst (filter Q fm) f.
Proof.
Admitted.


(* Lemma fsubst_read {A B C : Type} `{Inhab B} (fm : fmap A B) (f : C -> A) x :
read (fsubst fm f) x = read fm (f x).
Admitted.

Lemma fsubst_empty {A B C : Type} `{Inhab B} (f : C -> A) :
fsubst (empty : fmap A B) f = empty.
Admitted. *)

Lemma fsubst_empty {A B C : Type} (f : A -> C) : 
  fsubst empty f = empty :> fmap C B.
Proof. Admitted.


Lemma fsubst_update_valid {A B C : Type} (f : A -> C) (fm : fmap A B) x y: 
  valid_subst fm f ->
  fsubst (update fm x y) f = update (fsubst fm f) (f x) y.
Proof. Admitted.
Lemma fsubst_update {A B C : Type} (f : A -> C) (g : C -> A) (fm : fmap A B) x y: 
  cancel f g ->
  fsubst (update fm x y) f = update (fsubst fm f) (f x) y.
Proof.
  move=> c; apply/fsubst_update_valid=> > /(congr1 g) /[! c]-> //.
Qed.


Lemma fsubst_single {A B C : Type} (f : A -> C) (g : C -> A) (x : A) (y : B) :
  cancel f g ->
  fsubst (single x y) f = single (f x) y.
Proof.
  move=> c.
  by rewrite ?update_empty (fsubst_update _ _ _ c) // fsubst_empty.
Qed.

Lemma fsubstK {A B C : Type} (f : A -> C) (g : C -> A) : 
  cancel f g ->
  cancel g f ->
  @cancel (fmap A B) (fmap C B) (fsubst^~ g) (fsubst ^~ f).
Proof.
  move=> c1 c2. 
  elim/fmap_ind=> [|fm x y IHfm D].
  { by rewrite ?fsubst_empty. }
  do ? erewrite fsubst_update; eauto.
  by rewrite c2 IHfm.
  (* move=> D'; apply: D; move: D'.
  elim/fmap_ind: {IHfm} fm=> [|fm z {}y IH D].
  { by rewrite fsubst_empty. }
  erewrite fsubst_update; eauto.
  rewrite ?indom_update_eq=> -[/(can_inj c2)|/IH]; by autos*. *)
Qed.

Lemma fsubst_indom {A B C : Type} (f : A -> C) g (fm : fmap A B) x :
  cancel f g -> 
  cancel g f ->
  indom (fsubst fm f) (f x) = indom fm x.
Proof.
Admitted.

Lemma fsubst_read {A B C : Type} `{Inhab B} (f : A -> C) g (fm : fmap A B) x :
  cancel f g -> 
  cancel g f ->
  read (fsubst fm f) (f x) = read fm x.
Proof.
Admitted.

Lemma fsubst_remove {A B C : Type} (f : A -> C) g (fm : fmap A B) x : 
  cancel f g -> 
  cancel g f ->
  remove (fsubst fm f) (f x) = fsubst (remove fm x) f.
Proof.
Admitted.

Lemma filter_eq {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) `{Inhab B} : 
  (forall y x, P y x -> read fs1 y = read fs2 y) -> 
  filter P fs1 = filter P fs2.
Proof.
Admitted.

Lemma filter_in {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) `{Inhab B} x y : 
  P y x ->
  read (filter P fs) y = read fs y.
Proof.
Admitted.

Lemma filter_indom {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) y `{Inhab B} : 
  indom (filter P fs) y <-> (indom fs y /\ exists x, P y x).
Proof.
Admitted.

Lemma read_arb {A B : Type} (fs : fmap A B) x  `{Inhab B}: 
  ~ indom fs x -> read fs x = arbitrary.
Proof.
Admitted.

Lemma disj_filter {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) : 
  disjoint fs1 fs2 -> disjoint fs1 (filter P fs2).
Admitted.

Lemma filter_union {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) :
  disjoint fs1 fs2 ->
  filter P (fs1 \+ fs2) = filter P fs1 \+ filter P fs2.
Proof.
Admitted.

Lemma filter_union' {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) :
  (forall x y y', P x y <-> P x y') -> 
  filter P (fs1 \+ fs2) = filter P fs1 \+ filter P fs2.
Proof.
  case: fs1 fs2=> f1 ? [f2 ?] E.
  apply/fmap_extens=> /= x.
  rewrite /map_filter /map_union /map_disjoint.
  case: (f1 x)=> // ?.
  case: classicT=> //; case: (f2 _)=> // ?. 
  by case: classicT=> // /E ? [].
Qed.

Lemma filter_filter  {A B : Type} (fm : fmap A B) (P Q : A -> B -> Prop) : 
  filter P (filter Q fm) = 
  filter (fun x y => P x y /\ Q x y) fm.
Proof.
Admitted.

Definition diff {A B} (fs1 fs2 : fmap A B) : fmap A B := 
  filter (fun x _ => ~indom fs2 x) fs1.

Notation "fs1 '\-' fs2" := (diff fs1 fs2) (at level 20, right associativity).


Lemma remove_diff {A B} (fm : fmap A B) `{Inhab B} x :
  remove fm x = fm \- (single x arbitrary).
Proof.
  apply/fmap_extens=> -?.
  rewrite /remove /= /map_remove /map_filter indom_single_eq.
  (do 2? case: classicT)=> ??; subst*; by case: (fmap_data _ _).
Qed.

Lemma diff0 {A B} (fs : fmap A B) : fs \- empty = fs.  Admitted.
Lemma diffxx {A B} (fs : fmap A B) : fs \- fs = empty.  Admitted.

Lemma diff_indom {A B} (fs1 fs2 : fmap A B) x:
  indom (fs1 \- fs2) x = (indom fs1 x /\ ~ indom fs2 x).
Admitted.

Lemma diff_upd {A} d (fs1 fs2 : fmap A unit) : 
  indom fs1 d ->
  fs1 \- fs2 = update (fs1 \- update fs2 d tt) d tt.
Admitted.

Lemma diff_disj {A B} (fm1 fm2 : fmap A B) : 
  disjoint (fm1 \- fm2) fm2.
Proof.
Admitted.

Lemma union_diff {A B} (fm1 fm2 : fmap A B) `{Inhab B} : 
  disjoint fm1 fm2 ->
  (fm1 \+ fm2) \- fm2 = fm1.
Proof.
Admitted.


Arguments diff_upd : clear implicits.


Lemma filter_union_compl {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) : 
  filter P fs \+ filter (fun x y => ~ (P x y)) fs = fs.
Admitted.

Lemma indom_update {A B : Type} {fm : fmap A B} {x y} :
  indom (update fm x y) x.
Admitted.

Lemma update_neq {A B : Type} {fm : fmap A B} {x y z} `{Inhab B} :
  z <> x -> 
  read (update fm x y) z = read fm z.
Admitted.

Lemma update_eq {A B : Type} {fm : fmap A B} {x y} `{Inhab B} :
  read (update fm x y) x = y.
Admitted.

(* Lemma indom_single {A B D : Type} {x : A} {y : B} (fm : fmap A D) `{Inhab D} :
  indom fm = indom (single x y) -> 
  fm = single x (read fm x).
Admitted. *)

Lemma fmapE'  {A B : Type} (fm1 fm2 : fmap A B) `{Inhab B} : 
  (fm1 = fm2) <-> (forall x, read fm1 x = read fm2 x).
Proof.
Admitted.

Lemma fmapE  {A B : Type} (fm1 fm2 : fmap A B) `{Inhab B} : 
  (fm1 = fm2) = (forall x, indom (fm1 \+ fm2) x -> read fm1 x = read fm2 x).
Proof.
Admitted.

Lemma fmap0E A B (fm : fmap A B) `{Inhab B} : 
  (fm = empty) = (forall x, indom fm x -> read fm x = arbitrary).
Proof.
Admitted.

Definition Union {T D S : Type} (l : fset T) (fs : T -> fmap D S) : fmap D S. Admitted.
Definition interval (x y : int) : fset int. Admitted.

Lemma intervalU x y : x < y -> interval x y = update (interval (x + 1) y) x tt.
Admitted.

Lemma intervalUr x y : x <= y -> interval x (y + 1) = update (interval x y) y tt.
Admitted.

Lemma intervalgt x y : x <= y -> interval y x = empty.
Admitted.

Lemma indom_interval x y z : indom (interval x y) z = (x <= z < y).
Admitted.

Lemma Union_upd {T A B} (x : T) (fs : fset T) (fsi : T -> fmap A B) : 
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  Union (update fs x tt) fsi = fsi x \+ Union fs fsi.
Admitted.

Lemma Union0 {T A B} (fsi : T -> fmap A B) : Union empty fsi = empty.
Admitted.

Lemma Union_union {T A B} (fs : fset T) (fsi1 fsi2 : T -> fmap A B) :
  Union fs fsi1 \+ Union fs fsi2 = Union fs (fun t => fsi1 t \+ fsi2 t).
Admitted.

Lemma disjoint_Union {T A B} (fs : fset T) (fsi : T -> fmap A B) fs' :
  ((disjoint (Union fs fsi) fs' = forall i, indom fs i -> disjoint (fsi i) fs') * 
  (disjoint fs' (Union fs fsi) = forall i, indom fs i -> disjoint (fsi i) fs'))%type.
Admitted.
  
Lemma indom_Union {T A B} (fs : fset T) (fsi : T -> fmap A B) x : 
  indom (Union fs fsi) x = exists f, indom fs f /\ indom (fsi f) x.
Admitted.

Lemma update_union_not_r' [A B : Type] `{Inhab B} (h1 : fmap A B) [h2 : fmap A B] [x : A] (v : B) :
  update (h1 \+ h2) x v = update h1 x v \+ h2.
Proof.  
  rewrite fmapE=> y ?.
  case: (prop_inv (y = x))=> [->|?].
  { rewrite ?(update_eq, read_union_l) // indom_update_eq; autos*. }
  rewrite update_neq //.
  case: (prop_inv (indom h1 y))=> ?.
  { rewrite 2?read_union_l // ?indom_union_eq; autos*.
    by rewrite update_neq. }
  rewrite ?read_union_r // indom_union_eq indom_single_eq; autos*.
Qed.

Lemma fsubst_union_valid {A B C : Type}  `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) :
  valid_subst fm1 f ->
  valid_subst (fm1 \+ fm2) f ->
    fsubst (fm1 \+ fm2) f = 
    fsubst fm1 f \+ fsubst fm2 f.
Proof.
  elim/fmap_ind: fm1 fm2.
  { by move=> *; rewrite fsubst_empty ?union_empty_l. }
  move=> fm1 x y IHfm1 ? fm2 ?; rewrite -update_union_not_r'=> ?.
  have?: valid_subst fm1 f.
  { apply/valid_subst_update; eauto. }
  have?: valid_subst (fm1 \+ fm2) f.
  { apply/valid_subst_update; eauto. }
  by rewrite ?fsubst_update_valid // IHfm1 // update_union_not_r'.
Qed.


Lemma fsubst_disjoint {A B C}  (fm1 fm2 : fmap A B) (f : A -> C) g : 
  cancel f g ->
  cancel g f ->
  disjoint fm1 fm2 -> 
    disjoint (fsubst fm1 f) (fsubst fm2 f).
Proof.
  move=> c1 c2 dj.
  apply/disjoint_of_not_indom_both=> x.
  rewrite -[x]c2 ?(fsubst_indom _ _ c1 c2).
  exact/disjoint_inv_not_indom_both.
Qed.

Lemma fsubst_union {A B C} `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) g : 
  cancel f g ->
  cancel g f ->
  fsubst (fm1 \+ fm2) f = fsubst fm1 f \+ fsubst fm2 f.
Proof.
  move=> c1 c2.
  elim/fmap_ind: fm1.
  { by rewrite fsubst_empty ?union_empty_l. }
  move=> fm ?? IH ?.
  by rewrite -update_union_not_r' ?(fsubst_update _ _ _ c1) IH update_union_not_r'.
Qed.

Lemma filter_update {A B : Type} (fs : fmap A B) x y (P : A -> B -> Prop) :
  (forall (x : A) (y y' : B), P x y <-> P x y') ->
  filter P (update fs x y) = If P x y then update (filter P fs) x y else filter P fs.
Admitted.

Lemma filter_empty {A B : Type} (P : A -> B -> Prop) : 
  filter P empty = empty.
Proof.
Admitted.

Lemma filter_fsubst {A B C} (fm : fmap A B) (f : A -> C) g (P : C -> Prop) : 
  cancel f g ->
  cancel g f ->
  filter (fun x _=> P x) (fsubst fm f) = 
  fsubst (filter (fun x _ => (P (f x))) fm) f.
Proof.
  move=> c1 c2.
  elim/fmap_ind: fm.
  { by rewrite ?(fsubst_empty, filter_empty). }
  move=> > IH ?.
  rewrite (fsubst_update _ _ _ c1) ?filter_update //.
  case: classicT=> //.
  by rewrite IH (fsubst_update _ _ _ c1).
Qed.

Lemma filter_fsubst_valid {A B C} (fm : fmap A B) (f : A -> C) (P : C -> Prop) : 
  valid_subst fm f ->
  filter (fun x _=> P x) (fsubst fm f) = 
  fsubst (filter (fun x _=> P (f x)) fm) f.
Proof.
  elim/fmap_ind: fm.
  { by rewrite ?(fsubst_empty, filter_empty). }
  move=> fm ?? IH ??.
  have ?: valid_subst fm f by (apply/valid_subst_update; eauto).
  rewrite fsubst_update_valid ?filter_update // IH //. 
  case: classicT; rewrite ?fsubst_update_valid //.
  exact/valid_subst_filter.
Qed.

Lemma fsubst_eq {A B C} (fm : fmap A B) (f : A -> C) (P : A -> Prop): 
  valid_subst fm f -> 
  (forall x, indom fm x -> (exists y, f y = f x /\ indom fm y /\ P y)) ->
  fsubst fm f =
  fsubst (filter (fun x _ => P x) fm) f.
Proof.
  move=> v PP.
  apply/fmap_extens=> ?; rewrite /fsubst /= /map_fsubst.
  case: classicT=> a.
  { case: classicT=> b. 
    { do ? case: (indefinite_description _); clear a b.
      move=> x [<-] ind y [E] ?.
      move: ind; rewrite /map_indom /map_filter.
      case: classicT=> //; case F: (fmap_data _ _)=> //.
      by rewrite -(v x y) // /indom /map_indom F. }
    case: (indefinite_description _).
    move=> x [?]?; subst.
    case: (PP x)=> // y []/(@eq_sym _ _ _) ? []*.
    case: b; exists y; splits; eauto.
    rewrite /map_indom /map_filter.
    case: classicT=> //; by case F: (fmap_data _ _). }
  case: classicT=> // ?; case: (indefinite_description _)=> ? [?] ind.
  subst; case: a; eexists; split; eauto.
  move: ind; rewrite /map_indom /map_filter.
  case: classicT=> //; by case F: (fmap_data _ _).
Qed.
(* 2023-03-25 11:36 *)
