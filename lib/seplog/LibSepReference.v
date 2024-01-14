(** * LibSepReference: Appendix - The Full Construction *)

(** This file provides a pretty-much end-to-end construction of
a weakest-precondition style characteristic formula generator
(the function named [wpgen] in [WPgen]), for a core
programming language with programs assumed to be in A-normal form.

This file is included by the chapters from the course. *)

Set Implicit Arguments.
From LGTM.lib.theory Require Export LibCore LibSepTLCbuffer.
From LGTM.lib.seplog Require Export LibSepVar LibSepFmap.
From LGTM.lib.theory Require Import LibFunExt LibLabType.

From mathcomp Require Import ssreflect ssrfun zify.

From Flocq Require Export Binary Bits Core.
From vcfloat Require Export FPCompCert FPLib.

Open Scope Z_scope.

Module Fmap := LibSepFmap. (* Short name for Fmap module. *)

(* ################################################################# *)
(** * Imports *)

(* ================================================================= *)
(** ** Extensionality Axioms *)

(** These standard extensionality axioms may also be found in
    the [LibAxiom.v] file associated with the TLC library. *)
(* Lemma updE A B (f g : A -> B) x y :
  upd f x y = (fun _ => y) \u_() *)


(* ================================================================= *)
(** ** Variables *)

(** The file [LibSepVar.v], whoses definitions are imported in the header to
    the present file, defines the type [var] as an alias for [string].
    It also provides the boolean function [var_eq x y] to compare two variables,
    and the tactic [case_var] to perform case analysis on expressions of the
    form [if var_eq x y then .. else ..] that appear in the goal. *)

(* ================================================================= *)
(** ** Finite Maps *)

(** The file [LibSepFmap.v], which is bound by the short name [Fmap] in the
    header, provides a formalization of finite maps. These maps are used to
    represent heaps in the semantics. The library provides a tactic called
    [fmap_disjoint] to automate disjointness proofs, and a tactic called
    [fmap_eq] for proving equalities between heaps modulo associativity and
    commutativity. Without these two tactics, pr oofs involving finite maps
    would be much more tedious and fragile. *)

(* ################################################################# *)
(** * Source Language *)

(* ================================================================= *)
(** ** Syntax *)

(** The grammar of primitive operations includes a number of operations. *)


Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_rand : prim
  | val_neg : prim
  | val_opp : prim
  | val_eq : prim
  | val_add : prim
  | val_float_add : prim
  | val_neq : prim
  | val_sub : prim
  | val_mul : prim
  | val_float_mkpair : prim
  | val_float_fma : prim
  | val_div : prim
  | val_mod : prim
  | val_le : prim
  | val_lt : prim
  | val_ge : prim
  | val_gt : prim
  | val_ptr_add : prim
  | val_alloc : prim
  | val_dealloc : prim
  | val_length : prim.

(** Locations are defined as natural numbers. *)

Definition loc : Type := nat.

Definition hloc D : Type := loc * D.

(** The null location corresponds to address zero. *)

Definition null D (d : D) : hloc D := (0%nat, d).

(** The grammar of closed values includes includes basic values such as [int]
    and [bool], but also locations, closures. It also includes two special
    values, [val_uninit] used in the formalization of arrays, and [val_error]
    used for stating semantics featuring error-propagation. *)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_float : binary64 -> val
  | val_floatpair : binary64 -> binary64 -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_uninit : val
  | val_error : val
  | val_header : nat -> val

(** The grammar of terms includes values, variables, functions, applications,
    sequence, let-bindings, and conditions. Sequences are redundant with
    let-bindings, but are useful in practice to avoid binding dummy names,
    and serve on numerous occasion as a warm-up before proving results on
    let-bindings. *)

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

Definition to_int (v : val) : int := 
  match v with
  | val_int i => i 
  | _ => 0
  end.

Lemma to_int_if P a b : 
  to_int (If P then a else b) = If P then to_int a else to_int b.
Proof. by case: classicT. Qed.

Definition float_unit : binary64 := Zconst Tdouble 0.

Definition to_float (v : val) : binary64 := 
  match v with 
  | val_float i => i 
  | _ => float_unit
  end.

Lemma to_float_if P a b : 
  to_float (If P then a else b) = If P then to_float a else to_float b.
Proof. by case: classicT. Qed.

Definition to_loc (v : val) : loc := 
  match v with 
  | val_loc v => v 
  | _         => 0%nat 
  end.

Definition add_val : val -> val -> val := 
  fun v1 v2 => 
    match v1, v2 with 
    | val_int v1, val_int v2 => val_int (v1 + v2)
    | _, _ => val_unit
    end.

Lemma add_val_comm : comm add_val.
Proof. move=> v1 v2; destruct v1, v2=> //=; fequals; lia. Qed.

Lemma add_val_assoc : assoc add_val.
Proof. move=> v1 v2 v3; destruct v1, v2, v3=> //=; fequals; lia. Qed.

Hint Resolve add_val_comm add_val_assoc : core.

Lemma val_int_eq i j : 
  (val_int i = val_int j) = (i = j).
Proof. by extens; split=> [[]|]->. Qed.

Lemma val_float_eq i j : 
  (val_float i = val_float j) = (i = j).
Proof. by extens; split=> [[]|]->. Qed.

(** A state consists of a finite map from location to values. Records and
    arrays are represented as sets of consecutive cells, preceeded by a
    header field describing the length of the block. *)

Definition state D : Type := fmap (hloc D) val.

(** The type [heap], a.k.a. [state]. By convention, the "state" refers to the
    full memory state when describing the semantics, while the "heap"
    potentially refers to only a fraction of the memory state, when definining
    Separation Logic predicates. *)

Definition hheap D : Type := state D.

Definition proj D (h : hheap D) d := 
  Fmap.filter (fun '(_, c) _ => c = d) h.

(* ================================================================= *)
(** ** Coq Tweaks *)

(** [h1 \u h2] is a notation for union of two heaps. *)

Notation "h1 \u h2" := (Fmap.union h1 h2)
  (at level 37, right associativity).

(** Implicit types associated with meta-variables. *)



(* Implicit Types f : var. *)
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types w r vf vx : val.
(* Implicit Types t : trm. *)
(* Implicit Types d : D. *)
(* Implicit Types h : heap. *)
(* Implicit Types s : state. *)

(** The types of values and heap values are inhabited. *)

(* Check @arbitrary. *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Defined.


(** Coercions to improve conciseness in the statment of evaluation rules. *)

Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_float : binary64 >-> val.
Coercion val_loc : loc >-> val.
Coercion val_prim : prim >-> val.

Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.

(* ================================================================= *)
(** ** Substitution *)

(** The standard capture-avoiding substitution, written [subst x v t]. *)

Fixpoint subst (y:var) (v':val) (t:trm) : trm :=
  let aux t := subst y v' t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val v') t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

(* ================================================================= *)
(** ** Semantics *)

(** Evaluation rules for unary operations are captured by the predicate
    [redupop op v1 v2], which asserts that [op v1] evaluates to [v2]. *)

Inductive evalunop : prim -> val -> val -> Prop :=
  | evalunop_neg : forall b1,
      evalunop val_neg (val_bool b1) (val_bool (LibBool.neg b1))
  | evalunop_opp : forall n1,
      evalunop val_opp (val_int n1) (val_int (- n1)).

(** Evaluation rules for binary operations are captured by the predicate
    [redupop op v1 v2 v3], which asserts that [op v1 v2] evaluates to [v3]. *)

Inductive evalbinop : val -> val -> val -> val -> Prop :=
  | evalbinop_eq : forall v1 v2,
      evalbinop val_eq v1 v2 (val_bool (isTrue (v1 = v2)))
  | evalbinop_neq : forall v1 v2,
      evalbinop val_neq v1 v2 (val_bool (isTrue (v1 <> v2)))
  | evalbinop_add : forall n1 n2,
      evalbinop val_add (val_int n1) (val_int n2) (val_int (n1 + n2))
  | evalbinop_float_add : forall f1 f2,
      evalbinop val_float_add (val_float f1) (val_float f2) (val_float (f1 + f2)%F64)
  | evalbinop_sub : forall n1 n2,
      evalbinop val_sub (val_int n1) (val_int n2) (val_int (n1 - n2))
  | evalbinop_mul : forall n1 n2,
      evalbinop val_mul (val_int n1) (val_int n2) (val_int (n1 * n2))
  | evalbinop_float_mkpair : forall f1 f2,
      evalbinop val_float_mkpair (val_float f1) (val_float f2) (val_floatpair f1 f2)
  | evalbinop_float_fma : forall (f1 f2 f3 : ftype Tdouble),
      evalbinop val_float_fma (val_floatpair f1 f2) (val_float f3) (val_float (BFMA f1 f2 f3))
  | evalbinop_div : forall n1 n2,
      n2 <> 0 ->
      evalbinop val_div (val_int n1) (val_int n2) (val_int (Z.quot n1 n2))
  | evalbinop_mod : forall n1 n2,
      n2 <> 0 ->
      evalbinop val_mod (val_int n1) (val_int n2) (val_int (Z.rem n1 n2))
  | evalbinop_le : forall n1 n2,
      evalbinop val_le (val_int n1) (val_int n2) (val_bool (isTrue (n1 <= n2)))
  | evalbinop_lt : forall n1 n2,
      evalbinop val_lt (val_int n1) (val_int n2) (val_bool (isTrue (n1 < n2)))
  | evalbinop_ge : forall n1 n2,
      evalbinop val_ge (val_int n1) (val_int n2) (val_bool (isTrue (n1 >= n2)))
  | evalbinop_gt : forall n1 n2,
      evalbinop val_gt (val_int n1) (val_int n2) (val_bool (isTrue (n1 > n2)))
  | evalbinop_ptr_add : forall p1 p2 n,
      (p2:int) = p1 + n ->
      evalbinop val_ptr_add (val_loc p1) (val_int n) (val_loc p2).

(** The predicate [trm_is_val t] asserts that [t] is a value. *)

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

(** Big-step evaluation judgement, written [eval s t s' v]. *)

Section eval1.

Context (D : Type) (d : D).

Implicit Types f : var.
Implicit Types v : val.

Definition least_feasible_array_loc {A B} h (L : list B) (p : loc) (a : A) :=
  forall p', disjoint (Fmap.hconseq L p' a) h -> (p', a) <> null a -> (p <= p')%Z.

Inductive eval1 : hheap D -> trm -> hheap D -> val -> Prop :=
  | eval1_val : forall s v,
      eval1 s (trm_val v) s v
  | eval1_fun : forall s x t1,
      eval1 s (trm_fun x t1) s (val_fun x t1)
  | eval1_fix : forall s f x t1,
      eval1 s (trm_fix f x t1) s (val_fix f x t1)
  | eval1_app_args : forall s1 s2 s3 s4 t1 t2 v1 v2 r,
      (~ trm_is_val t1 \/ ~ trm_is_val t2) ->
      eval1 s1 t1 s2 v1 ->
      eval1 s2 t2 s3 v2 ->
      eval1 s3 (trm_app v1 v2) s4 r ->
      eval1 s1 (trm_app t1 t2) s4 r
  | eval1_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval1 s1 (subst x v2 t1) s2 v ->
      eval1 s1 (trm_app v1 v2) s2 v
  | eval1_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval1 s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval1 s1 (trm_app v1 v2) s2 v
  | eval1_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval1 s1 t1 s2 v1 ->
      eval1 s2 t2 s3 v ->
      eval1 s1 (trm_seq t1 t2) s3 v
  | eval1_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval1 s1 t1 s2 v1 ->
      eval1 s2 (subst x v1 t2) s3 r ->
      eval1 s1 (trm_let x t1 t2) s3 r
  | eval1_if : forall s1 s2 b v t1 t2,
      eval1 s1 (if b then t1 else t2) s2 v ->
      eval1 s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval1_unop : forall op m v1 v,
      evalunop op v1 v ->
      eval1 m (op v1) m v
  | eval1_binop : forall op m v1 v2 v,
      evalbinop op v1 v2 v ->
      eval1 m (op v1 v2) m v
  | eval1_ref : forall s v p,
      (forall p',  ~ Fmap.indom s (p', d) -> (p <= p')%Z) ->
      ~ Fmap.indom s (p, d) ->
      eval1 s (val_ref v) (Fmap.update s (p, d) v) (val_loc p)
  | eval1_get : forall s p v,
      Fmap.indom s (p, d) ->
      v = Fmap.read s (p, d) ->
      eval1 s (val_get (val_loc p)) s v
  | eval1_set : forall s p v,
      Fmap.indom s (p, d) ->
      eval1 s (val_set (val_loc p) v) (Fmap.update s (p, d) v) val_unit
  | eval1_free : forall s p,
      Fmap.indom s (p, d) ->
      eval1 s (val_free (val_loc p)) (Fmap.remove s (p, d)) val_unit
  | eval1_alloc : forall k n sa sb p,
      sb = Fmap.hconseq (val_header k :: LibList.make k val_uninit) p d ->
      n = Z_of_nat k ->
      (p, d) <> null d ->
      Fmap.disjoint sa sb ->
      (* picking the least feasible location to make allocation points deterministic *)
      least_feasible_array_loc sa (val_header k :: LibList.make k val_uninit) p d ->
      eval1 sa (val_alloc (val_int n)) (Fmap.union sb sa) (val_loc p)
  | eval1_dealloc : forall k vs sa sb p,
      sb = Fmap.hconseq (val_header k :: vs) p d ->
      k = LibList.length vs ->
      Fmap.disjoint sa sb ->
      eval1 (Fmap.union sb sa) (val_dealloc (val_loc p)) sa val_unit
  | eval1_length : forall s p k,
      Fmap.indom s (p, d) ->
      (val_header k) = Fmap.read s (p, d) ->
      eval1 s (val_length (val_loc p)) s (val_int k).

(** Specialized eval1uation rules for addition and division, for avoiding the
    indirection via [eval1_binop] in the course. *)

Lemma eval1_add : forall s n1 n2,
  eval1 s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2)).
Proof using. intros. applys eval1_binop. applys evalbinop_add. Qed.

Lemma eval1_div : forall s n1 n2,
  n2 <> 0 ->
  eval1 s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2)).
Proof using. intros. applys eval1_binop. applys* evalbinop_div. Qed.

(** [eval1_like t1 t2] asserts that [t2] eval1uates like [t1]. In particular,
    this relation hold whenever [t2] reduces in small-step to [t1]. *)

Definition eval1_like (t1 t2:trm) : Prop :=
  forall s s' v, eval1 s t1 s' v -> eval1 s t2 s' v.

End eval1.

(* Section eval. *)

(* Inductive eval (D : Type) : fset D -> hheap D -> (D -> trm) -> hheap D -> (D -> val) -> Prop :=
  | eval_empty h ht hv : eval empty h ht h hv
  | eval_step  h1 h2 h3 ht d v hv fs : 
    ~ Fmap.indom fs d        ->
      eval1 d h1 (ht d) h2 v ->
      eval fs h2 ht h3 hv    ->
        eval (Fmap.update fs d tt) h1 ht h3 (upd hv d v). *)

Definition eval D (fs : fset D) (h : hheap D) (ht : D -> trm) (h' : hheap D) (hv : D -> val) : Prop :=
  (forall d, indom fs d -> eval1 d (proj h d) (ht d) (proj h' d) (hv d)) /\
  forall d, ~indom fs d -> proj h d = proj h' d.

Definition eval_like D (fs : fset D) ht1 ht2 : Prop :=
  forall s s' hv, eval fs s ht1 s' hv -> eval fs s ht2 s' hv.

Definition local D (fs : fset D) (h : hheap D) :=
  forall x d, indom h (x, d) -> indom fs d.

(* Lemma remove_union_not_r  [A B : Type] [h1 h2 : fmap A B] [x : A] :
  ~ indom h2 x -> 
  Fmap.remove h1 x \u h2 = Fmap.remove (h1 \u h2) x.
Proof. *)

Lemma eval1_frame D (d : D) t h1 h2 h fs v : 
  local fs h -> 
  ~ indom fs d ->
  eval1 d h1 t h2 v -> 
    eval1 d (h1 \+ h) t (h2 \+ h) v.
Proof.
  move=> l ?.
  have ? : forall x, ~ indom h (x, d) by move=> x /l.
  have ? : forall x s, ~ indom s (x, d) -> ~ indom (s \u h) (x, d).
  { move=> *. rewrite* indom_union_eq. }
  have ? : forall x s v, indom s (x, d) -> v = read s (x, d) -> v = read (s \u h) (x, d).
  { move=> *. rewrite* read_union_l. }
  have ? : forall x s, indom s (x, d) -> indom (s \u h) (x, d).
  { move=> *. rewrite* indom_union_eq. }
  elim=> *; rewrite -?update_union_not_r //; try by (econstructor; eauto).
  { rewrite remove_union_not_r //; by (econstructor; eauto). }
  { rewrite union_assoc. eapply eval1_alloc; eauto. 
    { rew_disjoint. split; auto.
      apply disjoint_of_not_indom_both.
      intros (pp, dd) H1 H2. subst. 
      rewrite hconseq_indom in H1. destruct H1 as (<- & _). eauto.
    }
    { hnf in *. intros p' H Hn. rew_disjoint.
      destruct H as (H & H'). revert H Hn. eauto.
    }
  }
  { rewrite union_assoc. eapply eval1_dealloc; eauto. 
    rew_disjoint. split; auto.
    apply disjoint_of_not_indom_both.
    intros (pp, dd) H1 H2. subst. 
    rewrite hconseq_indom in H1. destruct H1 as (<- & _). eauto.
  }
Qed.

Lemma eval_seq D fs : forall s1 s2 s3 (ht1 ht2 : D -> trm) hv1 hv,
  eval fs s1 ht1 s2 hv1 ->
  eval fs s2 ht2 s3 hv ->
  eval fs s1 (fun d => trm_seq (ht1 d) (ht2 d)) s3 hv.
Proof.
  move=> > [] ? E1 [? E2]; splits=> *; last rewrite -E2 ?E1 //.
  by apply/eval1_seq; eauto.
Qed.

Lemma eval_let D fs : forall s1 s2 s3 (ht1 ht2 : D -> trm) (x : D -> var) hv1 hv,
  eval fs s1 ht1 s2 hv1 ->
  eval fs s2 (fun d => subst (x d) (hv1 d) (ht2 d)) s3 hv ->
  eval fs s1 (fun d => trm_let (x d) (ht1 d) (ht2 d)) s3 hv.
Proof.
  move=> > []? E1[? E2]; splits=> *; last rewrite -E2 ?E1 //.
  by apply/eval1_let; eauto.
Qed.

Lemma eval_if D fs :  forall s1 s2 (b : D -> bool) hv ht1 ht2,
  eval fs s1 (fun d => if b d then ht1 d else ht2 d) s2 hv ->
  eval fs s1 (fun d => trm_if (val_bool (b d)) (ht1 d) (ht2 d)) s2 hv.
Proof.
  move=> > [] *; splits*=>*.
  by apply/eval1_if; eauto.
Qed.

Lemma eval_app_fun D fs : forall s1 s2 hv1 hv2 (x : D -> var) ht1 hv,
  (forall d, indom fs d -> hv1 d = val_fun (x d) (ht1 d)) ->
  eval fs s1 (fun d => subst (x d) (hv2 d) (ht1 d)) s2 hv ->
  eval fs s1 (fun d => trm_app (hv1 d) (hv2 d)) s2 hv.
Proof.
  move=> > ? -[]*; splits*=>*.
  by apply/eval1_app_fun; eauto.
Qed.

Lemma eval_app_fix D fs : forall s1 s2 hv1 hv2 (x f : D -> var) ht1 hv,
  (forall d, indom fs d -> hv1 d = val_fix (f d) (x d) (ht1 d)) ->
  eval fs s1 (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (ht1 d))) s2 hv ->
  eval fs s1 (fun d => trm_app (hv1 d) (hv2 d)) s2 hv.
  move=> >.
  move=> ? -[]*; splits*=>*.
  by apply/eval1_app_fix; eauto.
Qed.

Lemma eval_val D fs : forall s (hv : D -> val),
  eval fs s (fun d => trm_val (hv d)) s hv.
Proof.
  move=> *; splits*=>*.
  exact/eval1_val.
Qed.

Lemma eval_fun D fs : forall (x : D -> var) ht1 hv s,
  (forall d, indom fs d -> hv d = val_fun (x d) (ht1 d)) ->
  eval fs s (fun d => trm_fun (x d) (ht1 d)) s hv.
Proof.
  move=> > E1 *.
  splits*=>*; rewrite ?E1 //.
  exact/eval1_fun.
Qed.

Lemma eval_fix D fs : forall (f x : D -> var) ht1 hv s,
  (forall d, indom fs d -> hv d = val_fix (f d) (x d) (ht1 d)) ->
  eval fs s (fun d => trm_fix (f d) (x d) (ht1 d)) s hv.
Proof.
  move=> > E1 *; splits*=>*; rewrite ?E1 //.
  exact/eval1_fix.
Qed.

Lemma eval_hv D (fs : fset D) ht hv hv' s1 s2 :
  eval fs s1 ht s2 hv' ->
  (forall d, indom fs d -> hv d = hv' d) ->
  eval fs s1 ht s2 hv.
Proof. case=> ?? E; splits*=> * /[! E] //; eauto. Qed.

(* ################################################################# *)
(** * Heap Predicates *)

(** We next define heap predicates and establish their properties.
    All this material is wrapped in a module, allowing us to instantiate
    the functor from [LibSepSimpl] that defines the tactic [xsimpl]. *)

(* Module Type Domain.

Parameter type : Type.

End Domain. *)

(* Module SepSimplArgs (Dom : Domain). *)

Section SepSimplArgs.


Context {D : Type}.

(* ================================================================= *)
(** ** Hprop and Entailment *)

Declare Scope hprop_scope.
Open Scope hprop_scope.

(* Definition D := Dom.type. *)

(** The type of heap predicates is named [hhprop]. *)

Definition hhprop := hheap D -> Prop.

(* Definition hhprop := hheap D -> hhprop. *)

(** Implicit types for meta-variables. *)

Implicit Types P : Prop.
Implicit Types H : hhprop.
Implicit Types d : D.
Implicit Types Q : val->hhprop.

(** Entailment for heap predicates, written [H1 ==> H2]. This entailment
    is linear. *)

Definition himpl (H1 H2:hhprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55, 
  format "'[' H1 ']' '/  '  ==>  '/  ' '[' H2 ']'") : hprop_scope.

(** Entailment between postconditions, written [Q1 ===> Q2]. *)

Definition qimpl A (Q1 Q2:A->hhprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

(* ================================================================= *)
(** ** Definition of Heap Predicates *)

(** The core heap predicates are defined next, together with the
    associated notation:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [\Top] denotes the true heap predicate (affine)
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential quantifier
    - [\forall x, H] denotes a universal quantifier
    - [H1 \-* H2] denotes a magic wand between heap predicates
    - [Q1 \--* Q2] denotes a magic wand between postconditions. *)

Definition hempty : hhprop :=
  fun h => (h = Fmap.empty).

Definition hsingle (p:loc) (d : D) (v:val) : hhprop :=
  fun h => (h = Fmap.single (p, d) v).

Definition hstar (H1 H2 : hhprop) : hhprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Definition hmerge op vl (H1 H2 : hhprop) : hhprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ valid_intersect vl h1 h2 
                              /\ h = Fmap.merge op h1 h2.

Definition hexists A (J:A->hhprop) : hhprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hhprop) : hhprop :=
  fun h => forall x, J x h.

Definition hlocal (H : hhprop) (fs : fset D) :=
  H ==> local fs.

Lemma fsubst_labf_of {A B : Type} (g : B -> A) (fs : fset A) l (f : A -> B) :
  cancel (labf_of f) (labf_of g) ->
  fsubst (label (Lab l fs)) (labf_of f) = 
  label (Lab l (fsubst fs f)).
Proof.
  move=> /[dup]/labf_ofK ? c.
  elim/fset_ind: fs=> [|fs x].
  { by rewrite ?(label_empty, fsubst_empty). }
  rewrite label_update=> fE ?.
  rewrite (fsubst_update _ _ _ c) ?indom_label_eq; autos*.
  erewrite fsubst_update; eauto.
  by rewrite label_update fE.
Qed.

(* Lemma proj_fsubst_valid  (f g : D -> D) h d : 
  cancel g f -> 
  (forall x, indom h x -> indom h (x.1, g (f x.2))) ->
  valid_subst h (fun x => (x.1, f x.2)) ->
  proj (fsubst h (fun x => (x.1, f x.2))) d = 
  fsubst (proj h (g d)) (fun x => (x.1, f x.2)).
Proof.
  move=> c dom v; rewrite /proj.
  have->: (fun '(_, c) => fun=> c = d) = fun (x : loc * _) (_ : val)=> snd x = d.
  { by apply/fun_ext_1=> -[]. }
  rewrite filter_fsubst_valid //=.
  rewrite (fsubst_eq (fun '(_, c0) => c0 = g d)).
  { rewrite filter_filter; fequals.
    apply/(congr1 (fun x => filter x h)); extens=> -[] /= *.
    by split=> [[]|->]. }
  { exact/valid_subst_filter. }
  case=> l d'; rewrite filter_indom=> -[?][] /= _ <-.
  exists (l, g (f d')); splits=> //=; rewrite ?c //.
  rewrite filter_indom /=; split; last by (exists 0; rewrite c).
  move: (dom (l, d')); exact.
Qed. *)

Lemma proj_fsubst  (f g : D -> D) h d : 
  cancel f g ->
  cancel g f ->
  proj (fsubst h (fun '(x, d) => (x, f d))) d = 
  fsubst (proj h (g d)) (fun '(x, d) => (x, f d)).
Proof.
  move=> c1 c2.
  rewrite /proj.
  have->: (fun '(_, c) => fun=> c = d) = fun (x : loc * _) (_ : val)=> snd x = d.
  { by apply/fun_ext_1=> -[]. }
  have [c1' c2']:
    cancel (fun '(x, d) => (x:loc, f d)) (fun '(x, d) => (x, g d)) /\
    cancel (fun '(x, d) => (x:loc, g d)) (fun '(x, d) => (x, f d)).
  { split; by case=> >; rewrite (c1, c2). }
  erewrite filter_fsubst; eauto.
  do ? fequals.
  apply/fun_ext_1=> -[]/= _ ?.
  apply/fun_ext_1=> _; apply/prop_ext.
  by split=> [<-|->]; rewrite (c1, c2).
Qed.

Definition hsubst (H : hhprop) (f : D -> D) :=
  fun h => H (fsubst h (fun '(x, d) => (x, f d))).

Definition hsub (H : hhprop) (f : D -> D) :=
  fun h => 
    exists h', 
      fsubst h' (fun x => (x.1, f x.2)) = h  /\
      valid_subst h' (fun x => (x.1, f x.2)) /\
      H h'.


Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Declare Scope arr_scope.
Delimit Scope arr_scope with arr.

Notation "p '~⟨' l ',' x '⟩~>' v" := (hsingle p (Lab l%nat x) v) (at level 32, format "p  ~⟨ l ,  x ⟩~>  v") : hprop_scope.
Notation "p '~(' d ')~>' v" := (hsingle p d%arr v) (at level 32, format "p  ~( d )~>  v") : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 42, right associativity) : hprop_scope.

Notation "H1 '\(' m ',' p ')' H2" := (hmerge m p H1 H2)
  (at level 41, right associativity, format "H1  \( m ,  p )  H2") : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
    format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
    format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\{' x |-> f '}' H" := (hsubst H (fun x => f)) 
  (at level 39, x binder, H at level 50, right associativity,
  format "'[' \{ x  |->  f } ']' '/   '  H").

(** The remaining operators are defined in terms of the preivous above,
    rather than directly as functions over heaps. Doing so reduces the
    amount of proofs, by allowing to better leverage the tactic [xsimpl]. *)

Definition hpure (P:Prop) : hhprop :=
  \exists (p:P), \[].

Definition htop : hhprop :=
  \exists (H:hhprop), H.

Definition hhtop (fs : fset D) : hhprop :=
  \exists (H:hhprop), hstar H (hpure (hlocal H fs)).

Definition hwand (H1 H2 : hhprop) : hhprop :=
  \exists H0, H0 \* hpure ((H1 \* H0) ==> H2).

Definition hlollipop op vl (H1 H2 : hhprop) : hhprop :=
  \exists H0, H0 \* hpure ((H1 \(op, vl) H0) ==> H2).


Definition qwand A (Q1 Q2:A->hhprop) : hhprop :=
  \forall x, hwand (Q1 x) (Q2 x).

Definition hbig_fset {A} hop (fs : fset A) (f : A -> hhprop) : hhprop :=
  fset_fold \[] (fun a H => hop (f a) H) fs.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "\Top" := (htop) : hprop_scope.

Notation "\[Top d ]" := (hhtop d) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Notation "H1 '\-(' m , p ')' H2" := (hlollipop H1 H2 m p)
  (at level 43, right associativity, format "H1  \-( m ,  p )  H2") : hprop_scope.


Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.

Reserved Notation "'\*_' ( i <- r ) F"
  (at level 43, F at level 43, i, r at level 50,
            format "'[' \*_ ( i  <-  r ) '/  '  F ']'").

Reserved Notation "'\(' m , p ')_' ( i <- r ) F"
  (at level 43, F at level 43, i, r at level 50,
            format "'[' \( m ,  p )_ ( i  <-  r ) '/  '  F ']'").

Reserved Notation "'\(+)_' ( i <- r ) F"
  (at level 43, F at level 43, i, r at level 50,
            format "'[' \(+)_ ( i  <-  r ) '/  '  F ']'").

Notation "'\*_' ( i <- r ) F" :=
  (hbig_fset hstar r (fun i => F)) : nat_scope.

Notation "'\(' m , p ')_' ( i <- r ) F" :=
  (hbig_fset (hmerge m p) r (fun i => F)) : nat_scope.

(* Notation "'\(' m ')_' ( i <- r ) F" :=
  (hbig_fset m r (fun i => F)) : nat_scope. *)


(* ================================================================= *)
(** ** Basic Properties of Separation Logic Operators *)

(* ----------------------------------------------------------------- *)
(** *** Tactic for Automation *)

(** We set up [auto] to process goals of the form [h1 = h2] by calling
    [fmap_eq], which proves equality modulo associativity and commutativity. *)

Hint Extern 1 (_ = _ :> hheap _) => fmap_eq.

(** We also set up [auto] to process goals of the form [Fmap.disjoint h1 h2]
    by calling the tactic [fmap_disjoint], which essentially normalizes all
    disjointness goals and hypotheses, split all conjunctions, and invokes
    proof search with a base of hints specified in [LibSepFmap.v]. *)

Import Fmap.DisjointHints.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (Fmap.disjoint _ _) => fmap_disjoint_pre.

(* ----------------------------------------------------------------- *)
(** *** Properties of [himpl] and [qimpl] *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

Hint Resolve himpl_refl.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_trans_r : forall H2 H1 H3,
    H2 ==> H3 ->
    H1 ==> H2 ->
    H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans M2 M1. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma hprop_op_comm : forall (op:hhprop->hhprop->hhprop),
  (forall H1 H2, op H1 H2 ==> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. applys himpl_antisym; applys M. Qed.

Lemma qimpl_refl : forall A (Q:A->hhprop),
  Q ===> Q.
Proof using. intros. unfolds*. Qed.

Hint Resolve qimpl_refl.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hempty] *)

Lemma hempty_intro :
  \[] Fmap.empty.
Proof using. unfolds*. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = Fmap.empty.
Proof using. auto. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hstar] *)

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (Fmap.union h1 h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hmerge_intro m vd : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  valid_intersect vd h1 h2 ->
  (H1 \(m, vd) H2) (Fmap.merge m h1 h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = Fmap.union h1 h2.
Proof using. introv M. applys M. Qed.

Lemma hstar_comm : forall H1 H2,
    H1 \* H2 = H2 \* H1.
Proof using.
  applys hprop_op_comm. unfold hhprop, hstar. intros H1 H2.
  intros h (h1 & h2 & M1 & M2 & D' & U). rewrite~ Fmap.union_comm_of_disjoint in U.
  exists* h2 h1.
Qed.

Lemma hmerge_comm m vd : forall H1 H2,
  comm m ->
  H1 \(m, vd) H2 = H2 \(m, vd) H1.
Proof using.
  move=> ++ ?.
  applys hprop_op_comm. unfold hhprop, hmerge. intros H1 H2.
  intros h (h1 & h2 & M1 & M2 & D' & U). rewrite~ Fmap.merge_comm in U.
  exists* h2 h1; by rewrite valid_intersect_comm.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D''&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { applys* hstar_intro. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D''&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { applys* hstar_intro. } }
Qed.

Lemma hmerge_assoc m vd : forall H1 H2 H3,
  (forall x y, (vd x /\ vd y) <-> vd (m x y)) ->
  assoc m ->
  (H1 \(m, vd) H2) \(m, vd) H3 = H1 \(m, vd) (H2 \(m, vd) H3).
Proof using.
  intros H1 H2 H3 ??. applys himpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D''&U). subst h'.
    exists h1 (h2 \[[m]] h3). splits~. 
    { applys* hmerge_intro. 
      rewrite valid_intersect_comm valind_intersect_union_eq_r in D''=> //.
      rewrite* valid_intersect_comm. }
    { move: D''; rewrite valid_intersect_comm ?valind_intersect_union_eq_r=> //.
      rewrite valid_intersect_comm=> -[]; split=> //. }
    subst; apply/Fmap.merge_assoc. autos*. }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D''&U). subst h'.
    exists (h1 \[[m]] h2) h3. splits~. 
    { applys* hmerge_intro. 
      rewrite* valind_intersect_union_eq_r in D''. }
    { rewrite valid_intersect_comm.
      move: D''; rewrite ?valind_intersect_union_eq_r=> // -[]??.
      split; rewrite* valid_intersect_comm. }
    by subst; rewrite Fmap.merge_assoc. }
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D''&U). forwards E: hempty_inv M1. subst.
    rewrite~ Fmap.union_empty_l. }
  { intros M. exists (Fmap.empty:hheap D) h. splits~. { applys hempty_intro. } }
Qed.

Hint Resolve hstar_hempty_l : core.

Lemma hmerge_hempty_l m vd : forall H,
  \[] \(m, vd) H = H.
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D'&U). forwards E: hempty_inv M1. subst.
    rewrite~ Fmap.merge_empty_l. }
  { intros M. exists (Fmap.empty:hheap D) h. splits=> //.
    rewrite* merge_empty_l. }
Qed.


Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l. applys~ hstar_comm. applys~ hstar_hempty_l.
Qed.

Lemma hmerge_hempty_r m vd : forall H,
  H \(m, vd) \[] = H.
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D'&U). forwards E: hempty_inv M2. subst.
    rewrite~ Fmap.merge_empty_r. }
  { intros M. exists h (Fmap.empty:hheap D). splits=>//.
    rewrite* merge_empty_r. }
Qed.

Lemma hmerge_hstar : 
  hstar = hmerge (fun _ _ => 0) (fun=> False).
Proof.
  apply/fun_ext_2=> ??; extens=> ?; splits.
  { case/hstar_inv=> h1 [h2][?][?][?]->.
    exists h1 h2; splits*.
    { by rewrite -disjoint_valid_subst. }
    by rewrite -disjoint_union_merge. }
  rewrite /hmerge=> -[]h1[]h2[?][?][?]->.
  exists h1 h2; splits*.
  { by rewrite disjoint_valid_subst. }
  by rewrite -disjoint_union_merge // disjoint_valid_subst.
Qed.

Lemma hstar_hexists : forall A (J:A->hhprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D''&U). exists~ x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D''&U)). exists h1 h2. splits~. { exists~ x. } }
Qed.

Lemma hstar_hforall : forall H A (J:A->hhprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D'&U). intros x. exists~ h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M. do 2 rewrite (@hstar_comm H1). applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_l M1.
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_r M1.
Qed.

(* ----------------------------------------------------------------- *)
(** ***  Properties of [hpure] *)

Lemma hpure_intro : forall P,
  P ->
  \[P] Fmap.empty.
Proof using. introv M. exists M. unfolds*. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = Fmap.empty.
Proof using. introv (p&M). split~. Qed.

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hstar_hpure_r : forall P H h,
  (H \* \[P]) h = (H h /\ P).
Proof using.
  intros. rewrite hstar_comm. rewrite hstar_hpure_l. apply* prop_ext.
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using. introv HP W. intros h K. rewrite* hstar_hpure_l. Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using.
  introv M. rewrite <- hstar_hpure_l. rewrite~ hstar_hempty_r.
Qed.

Lemma hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.
Proof using.
  introv M N. rewrite <- (hstar_hempty_l \[P]). rewrite~ hstar_hpure_r.
Qed.

Lemma himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].
Proof using. introv HP. intros h Hh. applys* hpure_intro_hempty. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using.
  introv W Hh. rewrite hstar_hpure_l in Hh. applys* W.
Qed.

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof using.
  applys himpl_antisym; intros h M.
  { applys* hpure_intro_hempty. }
  { forwards* : hpure_inv_hempty M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof using.
  intros. applys himpl_antisym; intros h; rewrite hstar_hpure_l; intros M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hexists] *)

Lemma hexists_intro : forall A (x:A) (J:A->hhprop) h,
  J x h ->
  (hexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hhprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.

Lemma himpl_hexists_l : forall A H (J:A->hhprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

Lemma himpl_hexists : forall A (J1 J2:A->hhprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hforall] *)

Lemma hforall_intro : forall A (J:A->hhprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hhprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

Lemma himpl_hforall_r : forall A (J:A->hhprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hhprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hhprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hhprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hwand] *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).
Proof using.
  unfold hwand. iff M.
  { rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    rewrite hstar_hexists. applys himpl_hexists_l. intros H.
    rewrite (hstar_comm H). rewrite hstar_assoc.
    rewrite (hstar_comm H H1). applys~ himpl_hstar_hpure_l. }
  { applys himpl_hexists_r H0.
    rewrite <- (hstar_hempty_r H0) at 1.
    applys himpl_frame_r. applys himpl_hempty_hpure M. }
Qed.

Lemma himpl_hwand_r : forall H1 H2 H3,
  H2 \* H1 ==> H3 ->
  H1 ==> (H2 \-* H3).
Proof using. introv M. rewrite~ hwand_equiv. Qed.

Lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 \-* H3) ->
  H2 \* H1 ==> H3.
Proof using. introv M. rewrite~ <- hwand_equiv. Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. applys himpl_hwand_r_inv. applys himpl_refl. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. apply himpl_hwand_r. rewrite~ hstar_hempty_r. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- hstar_hempty_l at 1. applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_l. }
Qed.

Lemma hwand_hpure_l : forall P H,
  P ->
  (\[P] \-* H) = H.
Proof using.
  introv HP. applys himpl_antisym.
  { lets K: hwand_cancel \[P] H. applys himpl_trans K.
    applys* himpl_hstar_hpure_r. }
  { rewrite hwand_equiv. applys* himpl_hstar_hpure_l. }
Qed.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. apply himpl_hwand_r. apply himpl_hwand_r.
  rewrite <- hstar_assoc. rewrite (hstar_comm H1 H2).
  applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. rewrite hwand_equiv. rewrite (hstar_comm H1 H2).
  rewrite hstar_assoc. applys himpl_hstar_trans_r.
  { applys hwand_cancel. } { applys hwand_cancel. }
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.

Lemma hwand_inv : forall h1 h2 H1 H2,
  (H1 \-* H2) h2 ->
  H1 h1 ->
  Fmap.disjoint h1 h2 ->
  H2 (h1 \u h2).
Proof using.
  introv M2 M1 D'. unfolds hwand. lets (H0&M3): hexists_inv M2.
  lets (h0&h3&P1&P3&D''&U): hstar_inv M3. lets (P4&E3): hpure_inv P3.
  subst h2 h3. rewrite union_empty_r in D' M3 M2 *. applys P4. applys* hstar_intro.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of qwand *)

Lemma qwand_equiv : forall H A (Q1 Q2:A->hhprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros x. rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    applys himpl_trans. applys hstar_hforall. simpl.
    applys himpl_hforall_l x. rewrite hstar_comm. applys hwand_cancel. }
  { applys himpl_hforall_r. intros x. rewrite* hwand_equiv. }
Qed.

Lemma qwand_cancel : forall A (Q1 Q2:A->hhprop),
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hhprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hhprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Arguments qwand_specialize [ A ].

(* ----------------------------------------------------------------- *)
(** *** Properties of [htop] *)

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. exists~ (=h). Qed.

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. intros. intros h Hh. applys* htop_intro. Qed.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof using. auto. Qed.

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { rewrite <- hstar_hempty_r at 1. applys himpl_frame_r. applys himpl_htop_r. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hsingle] *)

Lemma hsingle_intro : forall p d v,
  (p ~(d)~> v) (Fmap.single (p, d) v).
Proof using. intros. hnfs*. Qed.

Lemma hsingle_inv: forall p d v h,
  (p ~(d)~> v) h ->
  h = Fmap.single (p,d) v.
Proof using. auto. Qed.

Lemma hstar_hsingle_same_loc : forall p d w1 w2,
  (p ~(d)~> w1) \* (p ~(d)~> w2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D'&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

Arguments hstar_hsingle_same_loc : clear implicits.

(* ----------------------------------------------------------------- *)
(** *** Definition and Properties of [haffine] and [hgc] *)

Definition haffine (H:hhprop) :=
  True.

Lemma haffine_hany : forall (H:hhprop),
  haffine H.
Proof using. unfold haffine. auto. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using. applys haffine_hany. Qed.

Definition hgc := (* equivalent to [\exists H, \[haffine H] \* H] *)
  htop.

Notation "\GC" := (hgc) : hprop_scope.

Lemma haffine_hgc :
  haffine \GC.
Proof using. applys haffine_hany. Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. applys himpl_htop_r. Qed.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using. applys hstar_htop_htop. Qed.

Lemma hsubst_hempty f g :
  cancel f g ->
  cancel g f -> 
  \{ x |-> f x } \[] = \[].
Proof.
  move=> c1 c2.
  apply fun_ext_1=> fm; rewrite /hempty /hsubst.
  apply/prop_ext; split=> [|-> /[! @fsubst_empty]//].
  move/(congr1 (fsubst^~ (fun '(x, d) => (x, g d)))).
  by rewrite fsubstK ?fsubst_empty // => -[??]; rewrite (c1, c2).
Qed.

Lemma hsubst_hpure f g P : 
  cancel f g ->
  cancel g f -> 
  \{ x |-> f x } \[P] = \[P].
Proof.
  move=> c1 c2.
  apply fun_ext_1=> fm; rewrite /hempty /hpure /hexists /hsubst.
  fequals; apply fun_ext_1=> ?.
  by rewrite -{2}(hsubst_hempty c1 c2).
Qed.

Lemma hsubst_htop f :
  \{x |-> f x} \Top = \Top.
Proof.
  apply/fun_ext_1=> ?; rewrite /hsubst; apply/prop_ext. 
  split=> ?; exact/htop_intro.
Qed.


Lemma hsubst_hsingle f g d x p: 
  cancel f g ->
  cancel g f -> 
  \{ x |-> f x } p ~(d)~> x = p ~(g d)~> x.
Proof.
  move=> c1 c2.
  apply fun_ext_1=> fm; rewrite /hsingle /hsubst.
  apply/prop_ext; split=> [|->].
  { move/(congr1 (fsubst^~ (fun '(x, d) => (x, g d)))).
    rewrite fsubstK; rewrite ?fsubst_single ?(fsubst_single (g := fun '(x, d) => (x, f d)))=> //.
    all: by case=>??; rewrite (c1, c2). }
  rewrite ?(fsubst_single (g := fun '(x, d) => (x, g d))) ?c2 //.
  by case=>??; rewrite (c1, c2).
Qed.

Lemma hsubst_hstar f g H1 H2 :
  cancel f g ->
  cancel g f -> 
  \{x |-> f x} H1 \* H2 = (\{x |-> f x} H1) \* (\{x |-> f x} H2).
Proof.
  move=> c1 c2.
  have [c1' c2']:
    cancel (fun '(x, d) => (x:loc, f d)) (fun '(x, d) => (x, g d)) /\
    cancel (fun '(x, d) => (x:loc, g d)) (fun '(x, d) => (x, f d)).
  { split; by case=> >; rewrite (c1, c2). }
  apply fun_ext_1=> fm; rewrite /hstar /hsubst.
  apply/prop_ext; split; first last.
  { case=> h1 [h2] [?][?][?]->.
    do 2? eexists; do ? split; [eauto|eauto| | ]. 
    { by apply (fsubst_disjoint (g := fun '(x, d) => (x, g d))). }
    erewrite fsubst_union; eauto. }
  case=> h1 []h2 [?][?][?]E.
  exists (fsubst h1 (fun '(x, d) => (x, g d))), (fsubst h2 (fun '(x, d) => (x, g d))).
  rewrite -(fsubst_union _ _ c2' c1') -E ?fsubstK //; splits=> //.
  apply/fsubst_disjoint; eauto.
Qed.

(* Global Hint Rewrite hsubst_hempty hsubst_hsingle : hsubst. *)

(* ----------------------------------------------------------------- *)
(** *** Functor Instantiation to Obtain [xsimpl] *)

End SepSimplArgs.

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Declare Scope arr_scope.
Delimit Scope arr_scope with arr.

Notation "p '~⟨' l ',' x '⟩~>' v" := (hsingle p (Lab l%nat x) v) (at level 32, format "p  ~⟨ l ,  x ⟩~>  v") : hprop_scope.
Notation "p '~(' d ')~>' v" := (hsingle p d%arr v) (at level 32, format "p  ~( d )~>  v") : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 42, right associativity) : hprop_scope.

Notation "H1 '\(' m ',' p ')' H2" := (hmerge m p H1 H2)
  (at level 41, right associativity, format "H1  \( m ,  p )  H2") : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
    format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
    format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\{' x |-> f '}' H" := (hsubst H (fun x => f)) 
  (at level 39, x binder, H at level 50, right associativity,
  format "'[' \{ x  |->  f } ']' '/   '  H").

Notation "\GC" := (hgc) : hprop_scope.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (Fmap.disjoint _ _) => fmap_disjoint_pre.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "\Top" := (htop) : hprop_scope.

Notation "\[Top d ]" := (hhtop d) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Notation "H1 '\-(' m , p ')' H2" := (hlollipop H1 H2 m p)
  (at level 43, right associativity, format "H1  \-( m ,  p )  H2") : hprop_scope.


Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.

Reserved Notation "'\*_' ( i <- r ) F"
  (at level 43, F at level 43, i, r at level 50,
            format "'[' \*_ ( i  <-  r ) '/  '  F ']'").

Reserved Notation "'\(' m , p ')_' ( i <- r ) F"
  (at level 43, F at level 43, i, r at level 50,
            format "'[' \( m ,  p )_ ( i  <-  r ) '/  '  F ']'").

Reserved Notation "'\(+)_' ( i <- r ) F"
  (at level 43, F at level 43, i, r at level 50,
            format "'[' \(+)_ ( i  <-  r ) '/  '  F ']'").

Notation "'\*_' ( i <- r ) F" :=
  (hbig_fset hstar r (fun i => F)) : nat_scope.

Notation "'\(' m , p ')_' ( i <- r ) F" :=
  (hbig_fset (hmerge m p) r (fun i => F)) : nat_scope.


Notation "H1 ==> H2" := (himpl H1 H2) (at level 55, 
format "'[' H1 ']' '/  '  ==>  '/  ' '[' H2 ']'") : hprop_scope.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

(** We are now ready to instantiate the functor that defines [xsimpl].
    Demos of [xsimpl] are presented in chapter [Himpl.v]. *)

