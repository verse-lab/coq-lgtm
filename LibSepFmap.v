(** * LibSepFmap: Appendix - Finite Maps *)
Set Implicit Arguments.
From SLF Require Import LibCore.

From mathcomp Require Import ssreflect ssrfun.

Ltac eqsolve := solve [ intuition congruence | intuition discriminate ].

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

Definition valid_intersect {A B} `{Inhab B} (m : B -> B -> option A) (h1 h2 : fmap A B) : Prop :=
  forall x, indom h1 x -> indom h2 x -> m (read h1 x) (read h2 x) <> None.

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

Lemma disjoint_valid_subst h1 h2 `{Inhab B} : 
  disjoint h1 h2 = valid_intersect (fun _ _ => None) h1 h2.
Proof. rewrite disjoint_eq. by extens; split=> v ? /v/[apply]. Qed.


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

Lemma valid_intersect_sym `{Inhab B} m : forall h1 h2,
  (forall a b, m a b = m b a) -> 
  valid_intersect m h1 h2 ->
  valid_intersect m h2 h1.
Proof using. move=> h1 h2 pP v ? /v/[apply]; by rewrite pP. Qed.


Lemma valid_intersect_comm `{Inhab B} p : forall h1 h2,
  (forall a b, p a b = p b a) -> 
  valid_intersect p h1 h2 = valid_intersect p h2 h1.
Proof using. lets: valid_intersect_sym. extens*. Qed.

Lemma disjoint_comm : forall h1 h2,
  disjoint h1 h2 = disjoint h2 h1.
Proof using. lets: disjoint_sym. extens*. Qed.

Lemma disjoint_empty_l : forall h,
  \# empty h.
Proof using. intros [f F] x. simple~. Qed.

Lemma valid_intersect_empty_l `{Inhab B} p : forall h,
  valid_intersect p empty h.
Proof using. by move=> ?. Qed.


Lemma disjoint_empty_r : forall h,
  \# h empty.
Proof using. intros [f F] x. simple~. Qed.

Lemma valid_intersect_empty_r `{Inhab B} p : forall h,
  valid_intersect p h empty.
Proof using. by move=> ?. Qed.

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

(* Lemma disjoint_union_eq_r m : forall h1 h2 h3,
  valid_intersect  h1 (h2 \[[m]] h3) =
  (valid_intersect m h1 h2 /\ valid_intersect m h1 h3).
Proof using.
  intros [f1 F1] [f2 F2] [f3 F3].
  unfolds disjoint, union. simpls.
  unfolds map_disjoint, map_union. extens. iff M [M1 M2].
  split; intros x; specializes M x;
   destruct (f2 x); intuition; tryfalse.
  intros x. specializes M1 x. specializes M2 x.
   destruct (f2 x); intuition.
Qed. *)

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

Fixpoint hconseq [D:Type] (B:Type) (vs:list B) (l:nat) (d:D) : fmap (nat * D) B :=
  match vs with
  | nil => empty
  | v::vs' => (single (l, d) v) \+ (hconseq vs' (S l) d)
  end.

Lemma hconseq_nil : forall [D:Type] B (l:nat) (d : D),
  hconseq (@nil B) l d = empty.
Proof using. auto. Qed.

Lemma hconseq_cons : forall [D:Type] B (l:nat) (v:B) (vs:list B) (d : D),
  hconseq (v::vs) l d = (single (l, d) v) \+ (hconseq vs (S l) d).
Proof using. auto. Qed.

Lemma hconseq_cons' : forall [D:Type] B (l:nat) (v:B) (vs:list B) (d : D),
  hconseq (v::vs) l d = (single (l, d) v) \+ (hconseq vs (l+1) d).
Proof using. intros. math_rewrite (l+1 = S l)%nat. applys hconseq_cons. Qed.

Lemma hconseq_indom : forall [D:Type] B (vs:list B) (l:nat) (d : D) p d',
  indom (hconseq vs l d) (p, d') <-> d' = d /\ (l <= p < l + length vs)%nat.
Proof.
  intros D B vs. induction vs as [ | v vs IH ]; intros.
  { rewrite -> hconseq_nil, length_nil.
    unfolds indom, map_indom. simpl. split; intros; try eqsolve.
    math.
  }
  { rewrite -> hconseq_cons, indom_union_eq, indom_single_eq, IH, length_cons.
    split; intros H.
    { destruct H as [ HH | (<- & HH) ].
      { inversion HH. subst. split; auto. math. }
      { split; auto. math. }
    }
    { destruct H as (<- & H).
      destruct (Nat.eq_dec l p) as [ -> | ].
      { by left. }
      { right. split; auto. math. }
    }
  }
Qed.

Corollary disjoint_single_hconseq : forall [D:Type] B l l' L (v:B) (d:D),
  (l < l')%nat \/ (l >= l'+length L)%nat ->
  \# (single (l, d) v) (hconseq L l' d).
Proof using.
  intros. apply disjoint_of_not_indom_both.
  intros (pp, dd). rewrite hconseq_indom indom_single_eq.
  intros HH (_ & ?). inversion HH. subst. intuition math.
Qed.

Lemma hconseq_disjoint_suffcond1 : forall [D:Type] B (vs1 vs2:list B) (l1 l2:nat) (d1 d2 : D),
  d1 <> d2 -> disjoint (hconseq vs1 l1 d1) (hconseq vs2 l2 d2).
Proof.
  intros. apply disjoint_of_not_indom_both.
  intros (x, d'). rewrite ! hconseq_indom. eqsolve.
Qed.

Lemma hconseq_disjoint_nececond1 : forall [D:Type] B (vs1 vs2:list B) (l1 l2:nat) (d d' : D),
  disjoint (hconseq vs1 l1 d) (hconseq vs2 l2 d) ->
  d <> d' -> disjoint (hconseq vs1 l1 d') (hconseq vs2 l2 d').
Proof.
  intros. apply disjoint_of_not_indom_both. intros (x, d'') Ha Hb.
  rewrite -> hconseq_indom in Ha, Hb.
  destruct Ha as (<- & Ha), Hb as (_ & Hb).
  eapply disjoint_inv_not_indom_both with (x:=(x, d)).
  1: apply H.
  all: by rewrite hconseq_indom.
Qed.

Global Opaque hconseq.

Hint Rewrite hconseq_nil hconseq_cons : rew_listx.

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

From Coq Require Import Permutation.

Lemma remove_union_not_r  [A B : Type] [h1 h2 : fmap A B] [x : A] :
  ~ indom h2 x -> 
  remove h1 x \+ h2 = remove (h1 \+ h2) x.
Proof using.
  intros H. apply fmap_extens. intros y. 
  simpl. unfold map_union, map_remove. 
  case_if; auto_false. subst y. 
  unfolds indom, map_indom.
  case_eq (fmap_data h2 x); auto_false.
  (* ! *)
  eqsolve.
Qed.

(* fmap_fold seems not to be used. *)

(*
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
*)

(* Lemma fmap_foldE' A B (P : Type) (p : P) (f : A -> B -> P -> P) :
  (fmap_fold p f empty = p) *
  ( forall fm x y, fmap_fold p f (update fm x y) = f x y (fmap_fold p f fm)).
Admitted. *)

(* Going completely first-order to save time *)

Section Aux. 

Fixpoint get_only_some [A : Type] (l : list (option A)) : list A :=
  match l with
  | x :: l' => match x with Some y => y :: (get_only_some l') | None => (get_only_some l') end
  | nil => nil
  end.

Lemma map_fst_combine [A B : Type] (l1 : list A) (l2 : list B) :
  length l1 = length l2 ->
  LibList.map fst (combine l1 l2) = l1.
Proof.
  revert l2.
  induction l1 as [ | x l1 IH ]; intros.
  { destruct l2; [ | inversion H ]. auto. }
  { destruct l2; [ inversion H | ]. 
    rewrite -> combine_cons, -> map_cons.
    simpl. f_equal. apply IH. 
    rewrite -> ! length_cons in H. inversion H; auto.
  }
Qed.

Lemma mem_map_inv [A B : Type] (f : A -> B) (l : list A) y :
  mem y (LibList.map f l) -> exists x, mem x l /\ y = f x.
Proof.
  intros H. induction l as [ | x l IH ].
  { inversion H. }
  { rewrite -> map_cons in H. apply mem_cons_inv in H.
    destruct H as [ -> | H ].
    { exists x. split; auto. }
    { apply IH in H. destruct H as (x0 & H). exists x0. split. 1: constructor; auto. all: intuition. }
  }
Qed.

(* should do so from the beginning! *)

Fact length_List_length [A : Type] (l : list A) : length l = List.length l.
Proof. induction l; auto. rewrite -> length_cons. simpl. auto. Qed.

Fact mem_In [A : Type] (x : A) (l : list A) : mem x l <-> List.In x l.
Proof.
  induction l as [ | y l IH ].
  { split; intros H; inversion H. }
  { simpl. split; intros H.
    { apply mem_cons_inv in H. intuition. }
    { apply mem_cons. intuition. }
  }
Qed.

Fact noduplicates_NoDup [A : Type] (l : list A) : noduplicates l <-> List.NoDup l.
Proof.
  induction l as [ | x l IH ].
  { split; intros; constructor. }
  { split; intros H; inversion H; subst.
    { rewrite -> mem_In in H2. constructor; intuition. }
    { rewrite <- mem_In in H2. constructor; intuition. }
  }
Qed.

Lemma noduplicates_Permutation [A : Type] (l l' : list A) : noduplicates l -> noduplicates l' ->
  (forall x:A, mem x l <-> mem x l') -> Permutation l l'.
Proof.
  rewrite -> ! noduplicates_NoDup. 
  setoid_rewrite -> mem_In.
  apply NoDup_Permutation.
Qed.

Lemma fold_right_Permutation [A B : Type] (f : A -> B -> B) (b : B) (l l' : list A)
  (Hcomm : forall a b p, f a (f b p) = f b (f a p))
  (Hperm : Permutation l l') : fold_right f b l = fold_right f b l'.
Proof.
  induction Hperm.
  { auto. }
  { rewrite -> ! fold_right_cons, -> IHHperm. reflexivity. }
  { rewrite -> ! fold_right_cons. rewrite -> Hcomm. reflexivity. }
  { eqsolve. }
Qed.

End Aux. 

Section Supp.

Definition is_map_supp [A B : Type] (h : map A B) (l : list (A * B)) :=
  noduplicates (LibList.map fst l) /\
  (forall x : A, h x <> None -> mem x (LibList.map fst l)) /\
  (forall pa, mem pa l -> h (fst pa) = Some (snd pa)).

Fact is_map_supp_dom [A B : Type] (h : map A B) (l : list (A * B)) :
  is_map_supp h l ->
  (forall x : A, h x <> None <-> mem x (LibList.map fst l)).
Proof.
  intros.
  hnf in H. destruct H as (Hnodup & Ha & Hb).
  split. 1: intuition.
  intros HH. apply mem_map_inv in HH.
  destruct HH as (pa & HH & ->).
  apply Hb in HH. eqsolve.
Qed.

Lemma fmap_exact_dom_pre [A B : Type] (h : map A B) : 
  map_finite h ->
  sigT (fun l => is_map_supp h l).
Proof.
  intros H.
  unfolds map_finite.
  apply indefinite_description in H.
  destruct H as (l & H).
  remember (remove_duplicates (LibList.filter (fun x => h x <> None) l)) as la.
  assert (Hf : Forall (fun x => h x <> None) la).
  { rewrite -> Forall_eq_forall_mem.
    intros x Hmem. subst la. 
    rewrite -> mem_remove_duplicates in Hmem.
    apply mem_filter_inv in Hmem. intuition.
  }
  remember (get_only_some (LibList.map h la)) as lb.
  assert (Hl : length la = length lb).
  { subst lb. clear -Hf.
    induction la as [ | a la IH ]; auto.
    apply Forall_cons_inv in Hf. specializes IH Hf.
    rewrite -> map_cons. simpl.
    destruct (h a); try eqsolve.
    rewrite -> ! length_cons.
    simpl. f_equal. auto.
  }
  exists (combine la lb).
  split. 2: split.
  { rewrite -> map_fst_combine; auto.
    subst. apply noduplicates_remove_duplicates.
  }
  { intros. 
    rewrite -> map_fst_combine; auto.
    subst. rewrite -> mem_remove_duplicates. apply mem_filter; auto.
  }
  { subst lb.
    clear Heqla.
    induction la as [ | a la IH ]; intros.
    { inversion H0. }
    { rewrite -> map_cons in Hl, H0.
      apply Forall_cons_inv in Hf. 
      simpl in Hl, H0. destruct (h a) as [ a' | ] eqn:E; try eqsolve.
      rewrite -> ! length_cons in Hl.
      apply Nat.succ_inj in Hl.
      specializes IH Hf Hl.
      rewrite -> combine_cons in H0.
      apply mem_cons_inv in H0.
      destruct H0 as [ H0 | H0 ].
      { subst pa. simpl. auto. }
      { apply IH. auto. }
    }
  }
Qed.

Definition fmap_exact_dom [A B : Type] (h : fmap A B) :=
  @fmap_exact_dom_pre A B (fmap_data h) (fmap_finite h).

Fact supp_empty (A B : Type) : is_map_supp (@empty A B) nil.
Proof.
  hnf. split. 2: split.
  { constructor. }
  { intros. simpl in H. eqsolve. }
  { intros. inversion H. }
Qed.

Lemma supp_update [A B : Type] (h : fmap A B) (x : A) (y : B) (Hnotin : ~ indom h x) l :
  is_map_supp h l -> is_map_supp (update h x y) ((x, y) :: l).
Proof.
  intros.
  pose proof H as Hb'. apply is_map_supp_dom with (x:=x) in Hb'.
  hnf in H |- *.
  destruct H as (Hnodup & Ha & Hb).
  rewrite -> map_cons. cbn delta [fst] beta iota.
  split. 2: split.
  { constructor. 2: auto.
    rewrite <- Hb'. intuition.
  }
  { intros x0 H0.
    simpl in H0. unfolds map_union.
    case_if.
    { subst. constructor. }
    { apply Ha in H0. constructor. auto. }
  }
  { intros pa H.
    apply mem_cons_inv in H.
    simpl. unfolds map_union.
    destruct H as [ -> | H ].
    { simpl. case_if. reflexivity. }
    { specializes Hb H. case_if.
      { subst. eqsolve. }
      { auto. }
    }
  }
Qed.

Lemma supp_remove [A B : Type] (h : fmap A B) (x : A) (y : B) l :
  is_map_supp h ((x, y) :: l) -> is_map_supp (remove h x) l.
Proof.
  intros.
  pose proof H as Hb'. apply is_map_supp_dom with (x:=x) in Hb'.
  hnf in H |- *.
  destruct H as (Hnodup & Ha & Hb).
  rewrite -> map_cons in *. simpls.
  split. 2: split.
  { inversion Hnodup. auto. }
  { intros x0 H0.
    unfolds map_remove. 
    case_if.
    apply Ha in H0. inversion H0; eqsolve.
  }
  { intros pa H.
    unfolds map_remove. 
    case_if.
    { inversion Hnodup; subst.
      apply mem_map with (f:=fst) in H. auto_false.
    }
    { apply Hb. constructor. auto. }
  }
Qed.

(*
Lemma fmap_iso_1 [A B : Type] (h1 h2 : fmap A B) (l : list (A * B)) :
  is_map_supp h1 l -> 
  is_map_supp h2 l -> 
  h1 = h2.
Proof.
  intros H1 H2.
  apply fmap_extens. intros y.
  hnf in H1, H2.
  destruct H1 as (Hnodup & H1a & H1b), H2 as (_ & H2a & H2b).
  
  (* destruct (fmap_data h1 y) as [ t1 | ] eqn:E1, (fmap_data h2 y) as [ t2 | ] eqn:E2; auto. *)
Admitted.
*)
Lemma fmap_iso_2 [A B : Type] (h : fmap A B) (l1 l2 : list (A * B)) :
  is_map_supp h l1 -> 
  (forall pa, mem pa l1 <-> mem pa l2) ->
  noduplicates (LibList.map fst l2) ->
  is_map_supp h l2.
Proof.
  intros H HH.
  hnf in H |- *.
  destruct H as (Hnodup & Ha & Hb).
  split. 2: split.
  { auto. }
  { intros x H0.
    specializes Ha H0.
    apply mem_map_inv in Ha.
    destruct Ha as (pa & Ha).
    destruct (fmap_data h x) as [ y | ] eqn:E; try eqsolve.
    destruct Ha as (Ha & Efst).
    rewrite -> HH in Ha. 
    eapply mem_map'. 2: instantiate (1:=pa); auto. 
    auto.
  }
  { intros. apply Hb. apply HH. auto. }
Qed.

Lemma fmap_iso_3_onedir [A B : Type] (h : fmap A B) (l1 l2 : list (A * B)) :
  is_map_supp h l1 -> 
  is_map_supp h l2 ->
  (forall pa, mem pa l1 -> mem pa l2).
Proof.
  intros H1 H2.
  hnf in H1, H2.
  destruct H1 as (Hnodup1 & H1a & H1b), H2 as (Hnodup2 & H2a & H2b).
  intros (x, y) H.
  specializes H1b H.
  simpl in H1b. assert (H1b': fmap_data h x <> None) by eqsolve.
  specializes H2a H1b'.
  apply mem_map_inv in H2a.
  destruct H2a as ((x', y') & H' & ->).
  simpls.
  specializes H2b H'.
  simpls. eqsolve.
Qed.

Corollary fmap_iso_3 [A B : Type] (h : fmap A B) (l1 l2 : list (A * B)) :
  is_map_supp h l1 -> 
  is_map_supp h l2 ->
  (forall pa, mem pa l1 <-> mem pa l2).
Proof.
  intros. split.
  { apply fmap_iso_3_onedir with (h:=h); intuition. }
  { apply fmap_iso_3_onedir with (h:=h); intuition. }
Qed.

Corollary fmap_iso_3_fst [A B : Type] (h : fmap A B) (l1 l2 : list (A * B)) :
  is_map_supp h l1 -> 
  is_map_supp h l2 ->
  (forall x, mem x (LibList.map fst l1) <-> mem x (LibList.map fst l2)).
Proof.
  intros. pose proof (@fmap_iso_3 _ _ h _ _ H H0).
  split; intros HH.
  { apply mem_map_inv in HH. 
    destruct HH as ((x', y') & H' & ->). simpl.
    rewrite -> H1 in H'.
    eapply mem_map'; eauto.
  }
  { apply mem_map_inv in HH. 
    destruct HH as ((x', y') & H' & ->). simpl.
    rewrite <- H1 in H'.
    eapply mem_map'; eauto.
  }
Qed.

Corollary fmap_exact_dom_empty (A B : Type) : projT1 (fmap_exact_dom (@empty A B)) = nil.
Proof.
  destruct (fmap_exact_dom (@empty A B)) as (l & H).
  simpl.
  pose proof (supp_empty A B) as H'.
  pose proof (@fmap_iso_3 A B (@empty A B) l (@nil (A * B)) H H').
  destruct l as [ | pa l ]; auto.
  assert (mem pa (pa :: l)) as HH by constructor. rewrite -> H0 in HH. inversion HH.
Qed.

End Supp.

Definition fset_fold [A P : Type] (p : P) (f : A -> P -> P) (h : fset A) : P :=
  (fold_right f p (LibList.map fst (projT1 (fmap_exact_dom h)))).

Lemma fset_foldE A (P : Type) (p : P) (f : A -> P -> P) :
  (fset_fold p f empty = p) *
  ((forall (a b : A) (p : P), f a (f b p) = f b (f a p)) ->
    forall fs x, ~ indom fs x -> fset_fold p f (update fs x tt) = f x (fset_fold p f fs)).
Proof.
  unfolds fset_fold.
  split.
  { rewrite -> fmap_exact_dom_empty. auto. }
  { intros Hcomm. intros.
    destruct (fmap_exact_dom fs) as (l & H0), (fmap_exact_dom (update fs x tt)) as (l' & H1').
    simpl.
    pose proof (@supp_update A unit fs x tt H _ H0) as H1.
    pose proof (@fmap_iso_3_fst A unit _ _ _ H1 H1') as H2.
    pose proof (@noduplicates_Permutation _ _ _ (proj1 H1') (proj1 H1)) as H3.
    rewrite -> fold_right_Permutation with (l:=(LibList.map fst l')) (l':=x :: (LibList.map fst l)).
    2: auto.
    { rewrite -> fold_right_cons. auto. }
    { change x with (fst (x, tt)). rewrite <- map_cons. apply H3. intros. rewrite -> H2. reflexivity. }
  }
Qed.

Lemma disjoint_update {A B} x y (fm1 fm2 : fmap A B) : 
  disjoint (update fm1 x y) fm2 = (~ indom fm2 x /\ disjoint fm1 fm2).
Proof.
  extens. iff M.
  { hnf in M. split.
    { specializes M x. simpl in M. unfolds map_union. case_if. 
      destruct M; try eqsolve.
    }
    { hnf. intros x0. specializes M x0. simpl in M. unfolds map_union. case_if; eqsolve. }
  }
  { destruct M.
    hnf. intros x0. specializes H0 x0. destruct H0; try eqsolve.
    simpl. unfolds map_union. case_if; try eqsolve.
    subst. right. 
    destruct (fmap_data fm2 x0) eqn:E; try eqsolve.
    destruct (classicT (fmap_data fm2 x0 <> None)); try eqsolve. 
  }
Qed.

Lemma remove_update_self [A B : Type] (h : fmap A B) (x : A) (y : B) :
  fmap_data h x = Some y -> h = update (remove h x) x y.
Proof.
  intros. apply fmap_extens. intros x0.
  simpl. unfolds map_remove, map_union.
  case_if; subst; auto. case_if. auto.
Qed.

(* several different ways can achieve this. may revise if possible *)
Lemma fmap_ind A B : forall P : fmap A B -> Prop,
  P empty -> 
  (forall fs x y, P fs -> ~ indom fs x -> P (update fs x y)) -> forall fs, P fs.
Proof.
  intros.
  pose (Q:=fun n => forall h, length (projT1 (fmap_exact_dom h)) = n -> P h).
  enough (forall n, Q n).
  { specializes H1 (length (projT1 (fmap_exact_dom fs))).
    hnf in H1. apply H1. reflexivity. 
  }
  { intros n. induction n.
    { hnf. intros.
      apply length_zero_inv in H1. 
      assert (forall x, fmap_data h x = None) as Hempty.
      { intros x. destruct (fmap_data h x) as [ y | ] eqn:E; auto.
        destruct (fmap_exact_dom h) as (l & HH). simpl in H1. subst l.
        hnf in HH. destruct HH as (_ & HH & _).
        assert (fmap_data h x <> None) as Hq by eqsolve.
        specializes HH Hq. inversion HH.
      }
      assert (h = empty) as ->.
      { apply fmap_extens. simpl. auto. }
      auto.
    }
    { hnf. intros.
      destruct (fmap_exact_dom h) as (l & HH). simpl in H1. 
      destruct l as [ | (x, y) l ]. 1: inversion H1.
      rewrite -> length_cons in H1. apply Nat.succ_inj in H1.
      assert (fmap_data h x = Some y) as E.
      { destruct HH as (_ & _ & HH). specializes HH mem_here. eqsolve. }
      pose proof (@remove_update_self _ _ _ _ _ E) as Eh.
      rewrite -> Eh.
      apply H0. 2: rewrite -> indom_remove_eq; eqsolve.
      apply supp_remove in HH.
      apply IHn.

      destruct (fmap_exact_dom (remove h x)) as (l' & HH'). simpl.
      rewrite <- length_map with (f:=fst) in H1 |- *.
      rewrite -> length_List_length in H1 |- *.
      pose proof (@fmap_iso_3_fst _ _ _ _ _ HH' HH) as H2.
      pose proof (@noduplicates_Permutation _ _ _ (proj1 HH') (proj1 HH) H2) as H3.
      apply Permutation_length in H3.
      eqsolve.
    }
  }
Qed.

Lemma fset_ind A : forall P : fset A -> Prop,
  P empty -> 
  (forall fs x, P fs -> ~ indom fs x -> P (update fs x tt)) -> forall fs, P fs.
Proof. intros. apply fmap_ind; auto. intros fs0 x [ ]. revert fs0 x. auto. Qed.

Lemma fold_fset_eq {A P : Type} (fs : fset A) (f1 f2 : A -> P -> P) (p : P):
  (forall d, indom fs d -> f1 d = f2 d) ->
  fset_fold p f1 fs = fset_fold p f2 fs.
Proof.
  intros.
  unfold fset_fold.
  destruct (fmap_exact_dom fs) as (l & HH). simpl.
  assert (Forall (fun a => f1 a = f2 a) (LibList.map fst l)) as H0.
  { rewrite -> Forall_eq_forall_mem. intros.
    specializes H x. unfolds indom, map_indom.
    apply mem_map_inv in H0. destruct H0 as ((x0, []) & H0 & ->). simpls.
    destruct HH as (_ & _ & HH). specializes HH H0. apply H. simpls. eqsolve.
  }
  clear -H0.
  induction l; auto.
  rewrite -> map_cons in H0 |- *. 
  apply Forall_cons_inv in H0.
  rewrite -> ! fold_right_cons. eqsolve.
Qed.

Lemma update_empty {A B : Type} {x : A} {y : B} :
  single x y = update empty x y.
Proof. apply fmap_extens. intros. simpl. unfold map_union. case_if; eqsolve. Qed.

Lemma update_update {A B : Type} {x z : A} {y w : B} (fm : fmap A B) :
  x <> z ->
    update (update fm x y) z w = 
    update (update fm z w) x y.
Proof. intros. apply fmap_extens. intros. simpl. unfold map_union. 
  case_if; try eqsolve. case_if; try eqsolve. Qed.

Lemma update_updatexx {A B : Type} {x : A} {y w : B} (fm : fmap A B) :
    update (update fm x y) x w = 
    update fm x w.
Proof. apply fmap_extens. intros. simpl. unfold map_union. case_if; eqsolve. Qed.

Search sig.

Definition map_fsubst {A B C : Type} (fm : map A B) (f : A -> C) : map C B :=
  fun c =>
    match classicT (exists a, f a = c /\ map_indom fm a) with
    | left P => match indefinite_description P with (exist a _) => fm a end
    | _ => None
    end.

Program Definition fsubst {A B C : Type} (fm : fmap A B) (f : A -> C) : fmap C B := 
  make (map_fsubst fm f) _.
Next Obligation.
  pose proof (fmap_finite fm) as (l & H).
  exists (LibList.map f l).
  intros.
  unfold map_fsubst in H0.
  destruct (classicT (exists a : A, f a = x /\ map_indom fm a)) as [ N | N ]; try eqsolve.
  destruct N as (a & <- & Hdom).
  unfolds map_indom. specializes H Hdom. apply mem_map. auto.
Qed.

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



(* Lemma fsubst_read {A B C : Type} `{Inhab B} (fm : fmap A B) (f : C -> A) x :
read (fsubst fm f) x = read fm (f x).
Admitted.

Lemma fsubst_empty {A B C : Type} `{Inhab B} (f : C -> A) :
fsubst (empty : fmap A B) f = empty.
Admitted. *)

Lemma fsubst_empty {A B C : Type} (f : A -> C) : 
  fsubst empty f = empty :> fmap C B.
Proof. 
  apply fmap_extens. intros. simpl. unfold map_fsubst.
  destruct (classicT (exists a : A, f a = x /\ map_indom _ a)) as [ N | N ]; try eqsolve.
  destruct (indefinite_description N). reflexivity.
Qed.


Lemma fmapU_in1 {A B : Type} (fm1 fm2 : fmap A B) x : 
  indom fm1 x -> fmap_data (fm1 \+ fm2) x = fmap_data fm1 x.
Proof.
  rewrite /indom/map_indom/= /map_union.
  by case: (fmap_data _ _).
Qed.

Lemma fmapU_nin2 {A B : Type} (fm1 fm2 : fmap A B) x : 
  ~ indom fm2 x -> fmap_data (fm1 \+ fm2) x = fmap_data fm1 x.
Proof.
  move/not_not_inv=> E; rewrite /= /map_union E.
  by case: (fmap_data _ _).
Qed.

Lemma fmapU_nin1 {A B : Type} (fm1 fm2 : fmap A B) x : 
  ~ indom fm1 x -> fmap_data (fm1 \+ fm2) x = fmap_data fm2 x.
Proof.
  by move/not_not_inv=> E; rewrite /= /map_union E.
Qed.

Lemma fmapNone {A B : Type} (fm : fmap A B) x :
  ~indom fm x ->
  fmap_data fm x = None.
Proof. by move/not_not_inv. Qed.

Lemma fsubst_valid_indom  {A B C : Type} (f : A -> C) (fm : fmap A B) (x : C) :
    indom (fsubst fm f) x = 
    exists y, f y = x /\ indom fm y.
Proof.
  rewrite /fsubst /indom /= {1}/map_indom /map_fsubst.
  case: classicT=> pf.
  { case: (indefinite_description _); clear pf.
    move=> y [<-]?; extens; split=> //; eexists; eauto. }
  by extens.
Qed.

Lemma fsubst_update_valid {A B C : Type} (f : A -> C) (fm : fmap A B) x y: 
  injective f ->
  fsubst (update fm x y) f = update (fsubst fm f) (f x) y.
Proof.
  move=> inj.
  have?: forall h : fmap A B, valid_subst h f by move=> > /inj->.
  apply/fmap_extens=> z.
  case: (prop_inv (f x = z))=> [<-|?].
  { rewrite fsubst_valid_eq // /update ?fmapU_in1 ?indom_single_eq //=.
    by do ? case:classicT. }
  rewrite {2}/update fmapU_nin1 ?indom_single_eq //.
  case: (prop_inv (indom (fsubst (update fm x y) f) z))=> [|/[dup]?].
  { rewrite fsubst_valid_indom=> -[]w []?.
    rewrite indom_update_eq=> -[?|]; subst=> // ?.
    by rewrite ?fsubst_valid_eq // /update fmapU_nin1 // indom_single_eq=> /(congr1 f). }
  rewrite fsubst_valid_indom=> ind'.
  rewrite ?fmapNone // fsubst_valid_indom=> -[w][?]?; subst; apply:ind'. 
  exists w; split=> //; rewrite indom_update_eq; eauto.
Qed.

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

Lemma fsubst_iso {A B C : Type} (f : A -> C) g (fm : fmap A B) x : 
  cancel f g -> 
  cancel g f ->
  fmap_data (fsubst fm f) (f x) = fmap_data fm x.
Proof.
  intros. simpl. unfold map_fsubst.
  destruct classicT as [ N | N ].
  { destruct (indefinite_description _) as (x0 & (E' & HH)).
    apply f_equal with (f:=g) in E'. rewrite -> ! H in E'. eqsolve.
  }
  { destruct (fmap_data fm x) eqn:E; auto.
    assert (map_indom fm x) by eqsolve. false N. eauto.
  }
Qed.

Lemma fsubst_indom {A B C : Type} (f : A -> C) g (fm : fmap A B) x :
  cancel f g -> 
  cancel g f ->
  indom (fsubst fm f) (f x) = indom fm x.
Proof.
  intros.
  unfolds indom, map_indom. rewrite -> (@fsubst_iso _ _ _ f g); auto.
Qed.

Lemma fsubst_read {A B C : Type} `{Inhab B} (f : A -> C) g (fm : fmap A B) x :
  cancel f g -> 
  cancel g f ->
  read (fsubst fm f) (f x) = read fm x.
Proof.
  intros.
  unfolds read. rewrite -> (@fsubst_iso _ _ _ f g); auto.
Qed.

Lemma fsubst_remove {A B C : Type} (f : A -> C) g (fm : fmap A B) x : 
  cancel f g -> 
  cancel g f ->
  remove (fsubst fm f) (f x) = fsubst (remove fm x) f.
Proof.
  intros. apply fmap_extens. intros. 
  simpl. unfolds remove, map_remove. 
  cbn delta -[fsubst] beta iota. 
  case_if.
  { subst. unfold map_fsubst.
    destruct classicT as [ N | N ]; auto.
    destruct (indefinite_description _) as (x0 & (E' & HH)).
    apply f_equal with (f:=g) in E'. rewrite -> ! H in E'. subst. case_if. auto.
  }
  { unfold map_fsubst.
    destruct classicT as [ N | N ]; auto.
    all: destruct classicT as [ N2 | N2 ]; auto.
    { destruct (indefinite_description _) as (x' & (E' & HH)).
      destruct (indefinite_description _) as (x'' & (E'' & HH')).
      unfold map_indom in HH'. case_if.
      rewrite <- E'' in E'. 
      apply f_equal with (f:=g) in E'. rewrite -> ! H in E'. subst. auto.
    }
    { false N2. destruct N as (a & <- & N).
      exists a. split; auto.
      unfold map_indom. case_if. auto.
    }
    { false N. destruct N2 as (a & <- & N2).
      exists a. split; auto.
      unfolds map_indom. case_if. auto.
    }
  }
Qed.

Lemma filter_in {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) `{Inhab B} y: 
  P y (read fs y)->
  read (filter P fs) y = read fs y.
Proof.
  unfolds read, filter, map_filter. simpl.
  by case: fmap_data=> // ??; case: classicT.
Qed.

Lemma filter_indom {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) y `{Inhab B} : 
  indom (filter P fs) y <-> (indom fs y /\ P y (read fs y)).
Proof.
  unfolds indom, map_indom, filter, map_filter, read.
  simpl. destruct (fmap_data fs y) eqn:E. 2: eqsolve.
  case_if. 1: intuition eauto.
  by split=> // -[]_/C.
Qed.

Lemma filter_indom' {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) y : 
  indom (filter P fs) y -> 
  exists x, fmap_data fs y = Some x /\ indom fs y /\ P y x.
Proof.
  unfolds indom, map_indom, filter, map_filter, read.
  simpl. destruct (fmap_data fs y) eqn:E. 2: eqsolve.
  case_if. 1: intuition eauto. intros. by false H.
Qed.

Lemma read_arb {A B : Type} (fs : fmap A B) x  `{Inhab B}: 
  ~ indom fs x -> read fs x = arbitrary.
Proof. 
  intros. unfolds read. destruct (fmap_data fs x) eqn:E; auto. 
  false. apply H0. eqsolve.
Qed.

Lemma disj_filter {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) : 
  disjoint fs1 fs2 -> disjoint fs1 (filter P fs2).
Proof.
  intros. hnf in H |- *. intros x. specializes H x. destruct H; auto.
  right. unfolds filter, map_filter. simpl. rewrite -> H. auto. 
Qed.

Lemma filter_union {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) :
  disjoint fs1 fs2 ->
  filter P (fs1 \+ fs2) = filter P fs1 \+ filter P fs2.
Proof.
  intros. apply fmap_extens. intros x.
  simpl. unfolds map_filter, map_union.
  destruct (fmap_data fs1 x) eqn:E1, (fmap_data fs2 x) eqn:E2; try eqsolve.
  { hnf in H. specializes H x. eqsolve. }
  { case_if; eqsolve. }
Qed.

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
  apply fmap_extens. intros. simpl. unfolds map_filter. 
  destruct (fmap_data fm x) eqn:E; try eqsolve.
  repeat case_if; eqsolve.
Qed.

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

Lemma diff0 {A B} (fs : fmap A B) : fs \- empty = fs.
Proof.
  apply fmap_extens. intros. simpl. unfolds map_filter. 
  unfolds indom, map_indom. simpl. 
  case_if; try eqsolve. destruct (fmap_data fs x); eqsolve.
Qed.
Lemma diffxx {A B} (fs : fmap A B) : fs \- fs = empty.
Proof.
  apply fmap_extens. intros. simpl. unfolds map_filter. 
  destruct (fmap_data fs x) eqn:E; try eqsolve.
  unfolds indom, map_indom. case_if; eqsolve. 
Qed.

Lemma diff_indom {A B} (fs1 fs2 : fmap A B) x:
  indom (fs1 \- fs2) x = (indom fs1 x /\ ~ indom fs2 x).
Proof.
  extens. unfolds indom, map_indom. simpl. unfolds map_filter.
  unfolds indom, map_indom. 
  destruct (fmap_data fs1 x) eqn:E1, (fmap_data fs2 x) eqn:E2; try eqsolve.
  all: case_if; try eqsolve.
Qed.

Lemma filter_update {A B : Type} (fs : fmap A B) x y (P : A -> B -> Prop) :
  (forall (x : A) (y y' : B), P x y <-> P x y') ->
  filter P (update fs x y) = If P x y then update (filter P fs) x y else filter P fs.
Proof.
  intros. apply fmap_extens. intros x0. 
  case_if. 
  all: simpl; unfolds map_filter, map_union.
  { case_if; try subst; auto. case_if. auto. }
  { case_if; try subst; auto. case_if. 
    destruct (fmap_data fs x0) eqn:E; auto.
    specializes H x0 y b. rewrite -> H in C. case_if. auto.
  }
Qed.

Lemma diff_upd {A} d (fs1 fs2 : fmap A unit) : 
  indom fs1 d ->
  ~ indom fs2 d ->
  fs1 \- fs2 = update (fs1 \- update fs2 d tt) d tt.
Proof.
  intros.
  apply fmap_extens. intros. simpl. unfolds map_filter, map_union.
  unfolds indom, map_indom. simpl. unfolds map_union.
  destruct (fmap_data fs1 x) eqn:E1; (repeat (case_if; try subst)); try eqsolve.
  by case: (u).
Qed.


Lemma diff_disj {A B} (fm1 fm2 : fmap A B) : 
  disjoint (fm1 \- fm2) fm2.
Proof.
  hnf. intros. simpl. unfolds map_filter. 
  unfolds indom, map_indom.
  destruct (fmap_data fm1 x) eqn:E1; (repeat (case_if; try subst)); try eqsolve.
Qed.

Lemma union_diff {A B} (fm1 fm2 : fmap A B) `{Inhab B} : 
  disjoint fm1 fm2 ->
  (fm1 \+ fm2) \- fm2 = fm1.
Proof.
  intros. apply fmap_extens. intros. simpl. unfolds map_filter, map_union.
  unfolds indom, map_indom.
  destruct (fmap_data fm1 x) eqn:E1, (fmap_data fm2 x) eqn:E2; (repeat (case_if; try subst)); try eqsolve.
  specializes H0 x; eqsolve.
Qed.


Arguments diff_upd : clear implicits.


Lemma filter_union_compl {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) : 
  filter P fs \+ filter (fun x y => ~ (P x y)) fs = fs.
Proof.
  apply fmap_extens. intros. simpl. unfolds map_filter, map_union.
  destruct (fmap_data fs x) eqn:E; (repeat (case_if; try subst)); try eqsolve.
Qed.

Lemma filter_compl_disjoint {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) : 
  disjoint (filter P fs) (filter (fun x y => ~ (P x y)) fs).
Proof.
  apply disjoint_of_not_indom_both.
  intros x H1 H2. apply filter_indom' in H1, H2.
  destruct H1 as (? & E1 & H1 & ?), H2 as (? & E2 & H2 & ?).
  rewrite E1 in E2. injection E2 as <-. eqsolve.
Qed. 

Lemma indom_update {A B : Type} {fm : fmap A B} {x y} :
  indom (update fm x y) x.
Proof. 
  unfolds indom, map_indom. simpl. unfolds map_filter, map_union. case_if. eqsolve. 
Qed.

Lemma update_neq {A B : Type} {fm : fmap A B} {x y z} `{Inhab B} :
  z <> x -> 
  read (update fm x y) z = read fm z.
Proof.
  intros. unfolds read. simpl. unfolds map_filter, map_union. case_if. reflexivity. 
Qed.

Lemma update_eq {A B : Type} {fm : fmap A B} {x y} `{Inhab B} :
  read (update fm x y) x = y.
Proof.
  intros. unfolds read. simpl. unfolds map_filter, map_union. case_if. reflexivity. 
Qed.

Definition Union {T D S : Type} (l : fset T) (fs : T -> fmap D S) : fmap D S :=
  fset_fold (@empty D S) (fun (t : T) (h : fmap D S) => h \+ (fs t)) l.
Fixpoint interval_aux (base : int) (n : nat) : fset int :=
  match n with
  | O => empty
  | S n' => update (interval_aux base n') ((Z.of_nat n') + base) tt
  end.
Definition interval (x y : int) : fset int := 
  interval_aux x (Z.to_nat (y - x)).

Lemma indom_interval x y z : indom (interval x y) z = (x <= z < y).
Proof.
  remember (Z.to_nat (y - x)) as n.
  unfolds interval.
  rewrite <- Heqn.
  revert x y z Heqn.
  induction n as [ | n IH ]; intros.
  { simpl. unfolds indom, map_indom. simpl.
    extens. iff H; try eqsolve. math.
  }
  { simpl. rewrite -> indom_update_eq.
    assert (n = Z.to_nat ((y - 1) - x)) by math.
    assert (Z.of_nat n + x = y - 1) as -> by math.
    specializes IH z H.
    rewrite -> IH. extens. 
    transitivity (x <= z <= y - 1); try math.
    iff HH.
    { destruct HH as [ HH | HH ]; try math. }
    { destruct (Z.eq_dec z (y - 1)); try subst; try math.
      { left. reflexivity. }
      { right. math. }
    }
  }
Qed.

Lemma intervalgt x y : x <= y -> interval y x = empty.
Proof.
  intros. apply fmap_extens. intros z. simpl. 
  destruct (fmap_data (interval y x) z) eqn:E; auto.
  pose proof (indom_interval y x z) as HH.
  assert (indom (interval y x) z) as H0.
  { unfolds indom, map_indom. eqsolve. }
  rewrite -> HH in H0. math.
Qed.

Lemma intervalUr x y : x <= y -> interval x (y + 1) = update (interval x y) y tt.
Proof.
  intros. unfolds interval.
  replace (Z.to_nat (y + 1 - x)) with (S (Z.to_nat (y - x))) by math.
  simpl. f_equal. math.
Qed.

Lemma intervalU x y : x < y -> interval x y = update (interval (x + 1) y) x tt.
Proof.
  remember (Z.to_nat (y - x - 1)) as n.
  revert x y Heqn.
  induction n as [ | n IH ]; intros.
  { assert (y = x + 1) as -> by math.
    unfolds interval.
    replace (x + 1 - x) with 1 by math.
    replace (x + 1 - (x + 1)) with 0 by math.
    simpl. reflexivity.
  }
  { assert (y = n + x + 1 + 1) as -> by math.
    unfolds interval.
    replace (Z.to_nat (n + x + 1 + 1 - x)) with (S (S n)) by math.
    replace (Z.to_nat (n + x + 1 + 1 - (x + 1))) with (S n) by math.
    cbn delta [interval_aux] beta iota.
    specialize (IH x (n + x + 1)).
    replace (Z.to_nat (n + x + 1 - x)) with (S n) in IH by math.
    cbn delta [interval_aux] beta iota in IH.
    rewrite -> IH; try math.
    replace (Z.to_nat (n + x + 1 - (x + 1))) with n by math.
    replace (Z.of_nat n + (x + 1)) with (Z.of_nat (S n) + x) by math.
    apply update_update.
    math.
  }
Qed.

Lemma Union0 {T A B} (fsi : T -> fmap A B) : Union empty fsi = empty.
Proof. 
  unfold Union. unfolds fset_fold. rewrite -> fmap_exact_dom_empty, -> fold_right_nil. auto.
Qed.
(*
Lemma Union_union {T A B} (fs : fset T) (fsi1 fsi2 : T -> fmap A B) :
  Union fs fsi1 \+ Union fs fsi2 = Union fs (fun t => fsi1 t \+ fsi2 t).
Proof.
  unfold Union. unfolds fset_fold. 
  destruct (fmap_exact_dom fs) as (l & HH). simpl.
  destruct HH as (HH & _ & _).
  remember (LibList.map fst l) as lf. clear Heqlf.
  induction lf as [ | x lf IH ]. 
  { rewrite -> ! fold_right_nil. rewrite -> union_empty_l. auto. }
  { inversion HH; subst. specializes IH H2.
    rewrite -> ! fold_right_cons. 
    admit.
    (* ... *)
    (* need disjoint to swap *)
  }
Admitted.
*)
Lemma indom_Union {T A B} (fs : fset T) (fsi : T -> fmap A B) x : 
  indom (Union fs fsi) x = exists f, indom fs f /\ indom (fsi f) x.
Proof.
  (* should do induction on list *)
  unfold Union, fset_fold. 
  destruct (fmap_exact_dom fs) as (l & H). simpl.
  extens. transitivity (exists f, mem f (LibList.map fst l) /\ indom (fsi f) x).
  2:{
    pose proof (is_map_supp_dom H) as HH.
    setoid_rewrite <- HH. reflexivity.
  }
  clear H.
  induction l as [ | y l IH ].
  { rewrite -> fold_right_nil, map_nil.
    setoid_rewrite -> mem_In. simpl.
    unfolds indom, map_indom. simpl. intuition. firstorder.
  }
  { rewrite -> map_cons, -> fold_right_cons, -> indom_union_eq.
    destruct y as (y, []). simpl.
    setoid_rewrite -> mem_In. simpl. setoid_rewrite <- mem_In.
    rewrite -> IH.
    iff HH.
    { destruct HH as [ HH | HH ].
      { destruct HH as (? & ? & ?).
        eexists. split. 1: right; eauto. auto. 
      }
      { exists y. intuition. }
    }
    { destruct HH as (? & [ <- | ] & ?).
      { right. auto. }
      { left. eauto. }
    }
  }
Qed.

Lemma disjoint_Union {T A B} (fs : fset T) (fsi : T -> fmap A B) fs' :
  ((disjoint (Union fs fsi) fs' = forall i, indom fs i -> disjoint (fsi i) fs') * 
  (disjoint fs' (Union fs fsi) = forall i, indom fs i -> disjoint (fsi i) fs'))%type.
Proof.
  rewrite -> disjoint_comm. refine ((fun a => (a, a)) _).
  extens. 
  rewrite -> disjoint_eq. 
  setoid_rewrite -> disjoint_eq.
  setoid_rewrite -> indom_Union.
  firstorder.
Qed.

Lemma Union_upd_pre {T A B} (x : T) (fs : fset T) (fsi : T -> fmap A B) : 
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  ~ indom fs x ->
  Union (update fs x tt) fsi = fsi x \+ Union fs fsi.
Proof.
  intros.
  unfold Union.
  rewrite -> (snd (@fset_foldE _ _ _ _)).
  { rewrite -> union_comm_of_disjoint; auto.
    fold (Union fs fsi).
    rewrite -> (fst (@disjoint_Union _ _ _ _ _ _)).
    intros. apply H. unfolds indom, map_indom. eqsolve. 
  }
  { intros. destruct (classicT (a = b)) as [ -> | Hneq ]; auto.
    rewrite -> union_assoc, -> union_comm_of_disjoint with (h1:=fsi b).
    2: apply H; auto.
    rewrite <- union_assoc. auto.
  }
  { eqsolve. }
Qed.

Lemma Union_upd {T A B} (x : T) (fs : fset T) (fsi : T -> fmap A B) : 
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  Union (update fs x tt) fsi = fsi x \+ Union fs fsi.
Proof.
  intros.
  destruct (fmap_data fs x) eqn:E.
  { destruct u.
    pose proof (@remove_update_self _ _ _ _ _ E) as Eh. 
    rewrite -> Eh, -> update_updatexx.
    rewrite -> ! Union_upd_pre; auto.
    2:{ rewrite -> indom_remove_eq. eqsolve. }
    rewrite <- union_assoc, -> union_self. reflexivity.
  }
  { apply Union_upd_pre; auto. }
Qed.

Fact UnionN0 [T D S : Type] (fs : fset T) : Union fs (fun=> @empty D S) = empty.
Proof using.
  pattern fs. apply fset_ind; clear fs.
  { by rewrite -> Union0. }
  { intros. rewrite -> Union_upd. 2: auto. by rewrite -> H, -> union_empty_l. }
Qed.

Lemma update_union_not_r' [A B : Type] `{Inhab B} (h1 : fmap A B) [h2 : fmap A B] [x : A] (v : B) :
  update (h1 \+ h2) x v = update h1 x v \+ h2.
Proof.
  apply/fmap_extens=> y.
  case: (prop_inv (x = y))=> [->|].
  { rewrite /update ?fmapU_in1 // ?indom_union_eq indom_single_eq; eauto. }
  move=> ?.
  case: (prop_inv (indom h1 y))=> ?; rewrite /update.
  { rewrite fmapU_nin1 ?indom_single_eq // 2?fmapU_in1 // ?indom_union_eq; eauto.
    by rewrite fmapU_nin1 // indom_single_eq. }
  rewrite ?fmapU_nin1 // ?indom_union_eq ?indom_single_eq; autos*.
Qed.

Lemma fsubst_union_valid {A B C : Type}  `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) :
  valid_subst fm1 f ->
  valid_subst fm2 f ->
  valid_subst (fm1 \+ fm2) f ->
    fsubst (fm1 \+ fm2) f = 
    fsubst fm1 f \+ fsubst fm2 f.
Proof.
  move=> v1 v2 v3.
  apply/fmap_extens=> c.
  case: (prop_inv (indom (fsubst (fm1 \+ fm2) f) c))=>[|/[dup]?]; rewrite fsubst_valid_indom.
  { case=> y [<-]?; rewrite fsubst_valid_eq //.
    case: (prop_inv (indom fm1 y))=> ?.
    { rewrite ?fmapU_in1 // ?fsubst_valid_eq //.
      rewrite fsubst_valid_indom; by exists y. }
    rewrite ?fmapU_nin1 // ?fsubst_valid_eq // fsubst_valid_indom.
    case=> z []/v1; rewrite /indom /map_indom=> -> //. }
  move=> N; rewrite ?fmapNone // indom_union_eq ?fsubst_valid_indom=> -[].
  all: case=> z []??; case: N; exists z; split=> //; rewrite indom_union_eq; by (left+right). 
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

Lemma filter_empty {A B : Type} (P : A -> B -> Prop) : 
  filter P empty = empty.
Proof. 
  apply fmap_extens. intros x0. simpl; unfolds map_filter, map_union. auto. 
Qed.

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

Lemma hconseq_least_fresh_pre {D B : Type} (h : fmap (nat * D) B) (L : list B) (d : D) null :
  exists p, 
    disjoint (hconseq L p d) h /\ (p, d) <> null d.
Proof using.
  destruct (fmap_exact_dom h) as (ldom & (_ & Ha & Hb)).
  pose proof (loc_fresh_nat_ge ((fst (null d)) :: (LibList.map (fun t => fst (fst t)) ldom))) as (l & H).
  exists l. split.
  2:{ specialize (H 0%nat). destruct (null d) as (np, nd). intros HH. false H. rewrite -> Nat.add_0_r, -> mem_In. simpl. eqsolve. } 
  hnf. intros (p, d0). destruct (Nat.ltb p l) eqn:E.
  { rewrite -> Nat.ltb_lt in E. left. clear -E. revert l E d0. induction L as [ | y L IH ]; intros.
    { rewrite -> hconseq_nil. reflexivity. }
    { rewrite -> hconseq_cons. simpl. unfolds map_union. case_if; auto. 
      assert (p <> l) by math. eqsolve.
    }
  }
  { right. rewrite -> Nat.ltb_ge in E.
    specialize (H (p - l)%nat). replace (l+(p-l))%nat with p in H by math.
    destruct (fmap_data h (p, d0)) eqn:EE; auto.
    assert (mem (p, d0) (LibList.map fst ldom)) as Hm by (apply Ha; eqsolve).
    apply mem_map with (f:=fst) in Hm. simpl in Hm. rewrite -> LibList.map_map in Hm.
    false H. apply mem_cons. by right.
  }
Qed.

(* 2023-03-25 11:36 *)