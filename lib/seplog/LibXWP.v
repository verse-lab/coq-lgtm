Set Implicit Arguments.
From LGTM.lib.theory Require Export LibCore LibSepTLCbuffer.
From LGTM.lib.seplog Require Export LibSepVar LibSepFmap.
From LGTM.lib.theory Require Import LibFunExt LibLabType.
From LGTM.lib.seplog Require Import LibSepSimpl LibSepReference LibHypHeap LibWP.

From mathcomp Require Import ssreflect ssrfun zify.

Open Scope Z_scope.

Global Hint Extern 1 (_ = _ :> hheap _) => fmap_eq.

Tactic Notation "xstruct" :=
  applys @xstruct_lemma.

(** [xstruct_if_needed] removes the leading [mkstruct] if there is one. *)

Tactic Notation "xstruct_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Tactic Notation "xval" :=
  xstruct_if_needed; applys @xval_lemma.

Tactic Notation "xlet" :=
  xstruct_if_needed; applys @xlet_lemma.

Tactic Notation "xseq" :=
  xstruct_if_needed; applys @xseq_lemma.

Tactic Notation "xseq_xlet_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q =>
  match F with
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Tactic Notation "xif" :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys @xif_lemma; rew_bool_eq.

(** [xapp_try_clear_unit_result] implements some post-processing for
    cleaning up unused variables. *)

Tactic Notation "xapp_try_clear_unit_result" :=
  try match goal with |- (_ -> val) -> _ => intros _ end.

Tactic Notation "xhtriple" :=
  intros; applys @xhtriple_lemma.

Tactic Notation "xhtriple_if_needed" :=
  try match goal with |- @htriple _ ?t ?H ?Q => applys @xhtriple_lemma end.
    
(** [xapp_simpl] performs the final step of the tactic [xapp]. *)

 Lemma xapp_simpl_lemma {D : Type} : forall (F : formula) (H : hhprop D) Q,
  H ==> F Q ->
  H ==> F Q \* (Q \--* protect Q).
Proof using. introv M. xchange M. unfold protect. xsimpl. Qed.

Tactic Notation "xapp_simpl" :=
  first [ applys @xapp_simpl_lemma; do 2? xsimpl (* handles specification coming from [xfun] *)
        | (do 2? xsimpl); unfold protect; xapp_try_clear_unit_result ].

Tactic Notation "xapp_pre" :=
  xhtriple_if_needed; xseq_xlet_if_needed; xstruct_if_needed.

(** [xapp_nosubst E] implements the heart of [xapp E]. If the argument [E] was
    always a htriple, it would suffice to run [applys @xapp_lemma E; xapp_simpl].
    Yet, [E] might be an specification involving quantifiers. These quantifiers
    need to be first instantiated. This instantiation is achieved by means of
    the tactic [forwards_nounfold_then] offered by the TLC library. *)

Tactic Notation "xapp_nosubst" constr(E) :=
  xapp_pre;
  forwards_nounfold_then E ltac:(fun K => applys @xapp_lemma' K=>//; xapp_simpl).

(** [xapp_apply_spec] implements the heart of [xapp], when called without
    argument. If finds out the specification htriple, either in the hint data
    base named [htriple], or in the context by looking for an induction
    hypothesis. Disclaimer: as explained in [WPgen], the simple
    implementation of [xapp_apply_spec] which we use here does not apply when
    the specification includes premises that cannot be solved by [eauto];
    it such cases, the tactic [xapp E] must be called, providing the
    specification [E] explicitly. This limitation is overcome using more
    involved [Hint Extern] tricks in CFML 2.0. *)

Tactic Notation "xapp_apply_spec" :=
  first [ first [solve [ eauto with lhtriple ]| solve [ eauto with htriple ] ]
        | match goal with H: _ |- _ => eapply H end ].

(** [xapp_nosubst_for_records] is place holder for implementing [xapp] on
    records. It is implemented further on. *)

Ltac xapp_nosubst_for_records tt :=
  fail.

(** [xapp] first calls [xhtriple] if the goal is [htriple t H Q] instead
    of [H ==> wp t Q]. *)

Tactic Notation "xapp_nosubst" :=
  xapp_pre;
  first [ applys @xapp_lemma; [ xapp_apply_spec | xapp_simpl ]
        | xapp_nosubst_for_records tt ].

(** [xapp_try_subst] checks if the goal is of the form:
    - either [forall (r:val), (r = ...) -> ...]
    - or [forall (r:val), forall x, (r = ...) -> ...]

    in which case it substitutes [r] away. *)

Tactic Notation "xapp_try_subst" :=
  try match goal with
  | |- forall (r: _ ->val), (r = _) -> _ => intros ? ->
  | |- forall (r: _ ->val), forall x, (r = _) -> _ =>
      let y := fresh x in intros ? y ->; revert y
  end.

Tactic Notation "xapp" constr(E) :=
  rewrite ?label_single; (* we need to deal with a situations when the
   unary lemma is formulated for fs := single d tt
   but the goal's is ⟨_, single d tt⟩ *)
  xapp_nosubst E; first try typeclasses eauto; xapp_try_subst;
  rewrite -?label_single.

Tactic Notation "xapp" :=
  xapp_nosubst; xapp_try_subst.

Tactic Notation "xapp_big" constr(E) :=
  rewrite -> ! hbig_fset_hstar;
  xapp E=> //; rewrite -?hbig_fset_hstar.

Tactic Notation "xapp_debug" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys @xapp_lemma.

(** [xapp] is essentially equivalent to
    [ xapp_debug; [ xapp_apply_spec | xapp_simpl ] ]. *)

Tactic Notation "xfun" constr(S) :=
  xseq_xlet_if_needed; xstruct_if_needed; applys @xfun_spec_lemma S.

Tactic Notation "xfun" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys @xfun_nospec_lemma.

(** [xvars] may be called for unfolding "program variables as definitions",
    which take the form [Vars.x], and revealing the underlying string. *)

Tactic Notation "xvars" :=
  DefinitionsForVariables.libsepvar_unfold.

(** [xwp_simpl] is a specialized version of [simpl] to be used for
    getting the function [wp] to compute properly. *)

Ltac xwp_simpl :=
  xvars;
  cbn beta delta [
      var_eq subst
      string_dec string_rec string_rect
      sumbool_rec sumbool_rect
      Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
      Bool.bool_dec bool_rec bool_rect ] iota zeta;
  simpl; rewrite ?wpgenE; try (unfold subst; simpl).

Tactic Notation "xwp" :=
  intros;
  first [ applys @xwp_lemma_fun; [ reflexivity | ]
        | applys @xwp_lemma_fix; [ reflexivity | ] 
        | applys @wp_of_wpgen];
  xwp_simpl.

(* ================================================================= *)
(** ** Notations for Triples and [wpgen] *)

Declare Scope wp_scope.

(** Notation for printing proof obligations arising from [wpgen]. *)

Notation "'PRE' H 'CODE' F 'POST' Q" :=
  (H ==> (mkstruct F) Q)
  (at level 8, H at level 0, F, Q at level 0,
    format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

Notation "` F" :=
  (mkstruct F)
  (at level 10,
    format "` F") : wp_scope.

(** Custom grammar for the display of characteristic formulae. *)

Notation "<[ e ]>" :=
  e
  (at level 0, e custom wp at level 99) : wp_scope.

Notation "` F" :=
  (mkstruct F)
  (in custom wp at level 10,
    format "` F") : wp_scope.

Notation "( x )" :=
  x
  (in custom wp,
    x at level 99) : wp_scope.

Notation "{ x }" :=
  x
  (in custom wp at level 0,
    x constr,
    only parsing) : wp_scope.

Notation "x" :=
  x
  (in custom wp at level 0,
    x constr at level 0) : wp_scope.

Notation "'Fail'" :=
  ((wpgen_fail))
  (in custom wp at level 69) : wp_scope.

Notation "'Val' v" :=
  ((wpgen_val v))
  (in custom wp at level 69) : wp_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (in custom wp at level 69,
    x name, (* NOTE: For compilation with Coq 8.12, replace "name" with "ident",
                here and in the next 3 occurrences in the rest of the section. *)
    F1 custom wp at level 99,
    F2 custom wp at level 99,
    right associativity,
  format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'WP' [ d 'in' fs  '=>' t ] '{' v ',' Q '}'" := 
    (wp fs (fun d => t) (fun v => Q)) (at level 30, d name, v name,
  format "'[' 'WP'  [  d '['  'in'  ']' fs   '=>' '/    ' '['  t ']'  ] '/' '['   '{'  v ','  Q  '}' ']' ']' ") : wp_scope.

Notation "'Seq' F1 ; F2" :=
  ((wpgen_seq F1 F2))
  (in custom wp at level 68,
    F1 custom wp at level 99,
    F2 custom wp at level 99,
    right associativity,
    format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.

Notation "'App' '[' d 'in' fs ']' f v1" :=
  ((wp fs (fun d => trm_app (f d) (v1 d))))
  (in custom wp at level 68, d name, f, fs, v1 at level 0) : wp_scope.

Notation "'App' '[' d 'in' fs ']' f v1 v2" :=
  ((wp fs (fun d => trm_app (trm_app (f d) (v1 d)) (v2 d))))
  (in custom wp at level 68, d name, f, fs, v1, v2 at level 0) : wp_scope.

Notation "'If_' v 'Then' F1 'Else' F2" :=
  ((wpgen_if v F1 F2))
  (in custom wp at level 69,
    F1 custom wp at level 99,
    F2 custom wp at level 99,
    left associativity,
    format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Fun' x '=>' F1" :=
  ((wpgen_fun (fun x => F1)))
  (in custom wp at level 69,
    x name,
    F1 custom wp at level 99,
    right associativity,
  format "'[v' '[' 'Fun'  x  '=>'  F1  ']' ']'") : wp_scope.

Notation "'Fix' f x '=>' F1" :=
  ((wpgen_fix (fun f x => F1)))
  (in custom wp at level 69,
    f name, x name,
    F1 custom wp at level 99,
    right associativity,
    format "'[v' '[' 'Fix'  f  x  '=>'  F1  ']' ']'") : wp_scope.

(* ================================================================= *)
(** ** Notation for Concrete Terms *)

(** The custom grammar for [trm] is defined in [LibSepVar]. *)

Declare Scope val_scope.

(** Terms *)

Notation "<{ e }>" :=
  e
  (at level 0, e custom trm at level 99) : trm_scope.

Notation "( x )" :=
  x
  (in custom trm, x at level 99) : trm_scope.

Notation "'begin' e 'end'" :=
  e
  (in custom trm, e custom trm at level 99, only parsing) : trm_scope.

Notation "{ x }" :=
  x
  (in custom trm, x constr) : trm_scope.

Notation "x" := x
  (in custom trm at level 0,
    x constr at level 0) : trm_scope.

Notation "t1 t2" := (trm_app t1 t2)
  (in custom trm at level 30,
    left associativity,
    only parsing) : trm_scope.

Notation "'if' t0 'then' t1 'else' t2" :=
  (trm_if t0 t1 t2)
  (in custom trm at level 69,
    t0 custom trm at level 99,
    t1 custom trm at level 99,
    t2 custom trm at level 99,
    left associativity,
    format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'else' '/' '['   t2 ']' ']'") : trm_scope.

Notation "'if' t0 'then' t1 'end'" :=
  (trm_if t0 t1 (trm_val val_unit))
  (in custom trm at level 69,
    t0 custom trm at level 99, (* at level 0 ? *)
    t1 custom trm at level 99,
    left associativity,
    format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'end' ']'") : trm_scope.

Notation "t1 ';' t2" :=
  (trm_seq t1 t2)
  (in custom trm at level 68,
    t2 custom trm at level 99,
    right associativity,
    format "'[v' '[' t1 ']' ';' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'let' x '=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (in custom trm at level 69,
    x at level 0,
    t1 custom trm at level 99,
    t2 custom trm at level 99,
    right associativity,
    format "'[v' '[' 'let'  x  '='  t1  'in' ']' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'fix' f x1 '=>' t" :=
  (val_fix f x1 t)
  (in custom trm at level 69,
    f, x1 at level 0,
    t custom trm at level 99,
    format "'fix'  f  x1  '=>'  t") : val_scope.

Notation "'fix_' f x1 '=>' t" :=
  (trm_fix f x1 t)
  (in custom trm at level 69,
    f, x1 at level 0,
    t custom trm at level 99,
    format "'fix_'  f  x1  '=>'  t") : trm_scope.

Notation "'fun' x1 '=>' t" :=
  (val_fun x1 t)
  (in custom trm at level 69,
    x1 at level 0,
    t custom trm at level 99,
    format "'fun'  x1  '=>'  t") : val_scope.

Notation "'fun_' x1 '=>' t" :=
  (trm_fun x1 t)
  (in custom trm at level 69,
    x1 at level 0,
    t custom trm at level 99,
    format "'fun_'  x1  '=>'  t") : trm_scope.

Notation "()" :=
  (trm_val val_unit)
  (in custom trm at level 0) : trm_scope.

Notation "()" :=
  (val_unit)
  (at level 0) : val_scope.

(** Notation for Primitive Operations. *)

Notation "'ref'" :=
  (trm_val (val_prim val_ref))
  (in custom trm at level 0) : trm_scope.

Notation "'free'" :=
  (trm_val (val_prim val_free))
  (in custom trm at level 0) : trm_scope.

Notation "'not'" :=
  (trm_val (val_prim val_neg))
  (in custom trm at level 0) : trm_scope.

Notation "! t" :=
  (val_get t)
  (in custom trm at level 67,
    t custom trm at level 99) : trm_scope.

Notation "t1 := t2" :=
  (val_set t1 t2)
  (in custom trm at level 67) : trm_scope.

Notation "t1 + t2" :=
  (val_add t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 .+ t2" :=
  (val_float_add t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "'- t" :=
  (val_opp t)
  (in custom trm at level 57,
    t custom trm at level 99) : trm_scope.

Notation "t1 - t2" :=
  (val_sub t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 * t2" :=
  (val_mul t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 .* t2" :=
  (val_float_mkpair t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "'\fma' t1 t2 t3" :=
  (val_float_fma (val_floatpair t1 t2) t3)
  (in custom trm at level 58) : trm_scope.

Notation "t1 / t2" :=
  (val_div t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 'mod' t2" :=
  (val_mod t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 = t2" :=
  (val_eq t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 <> t2" :=
  (val_neq t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 <= t2" :=
  (val_le t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 < t2" :=
  (val_lt t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 >= t2" :=
  (val_ge t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 > t2" :=
  (val_gt t1 t2)
  (in custom trm at level 60) : trm_scope.

(* ================================================================= *)
(** ** Scopes, Coercions and Notations for Concrete Programs *)

Module ProgramSyntax.

Export NotationForVariables.

Module Vars := DefinitionsForVariables.

Close Scope fmap_scope.
Open Scope string_scope.
Open Scope val_scope.
Open Scope trm_scope.
Open Scope wp_scope.
Coercion string_to_var (x:string) : var := x.

End ProgramSyntax.


(* ================================================================= *)
(** ** Treatment of Functions of 2 and 3 Arguments *)

(** As explained in chapter [Struct], there are different ways to
    support functions of several arguments: curried functions, n-ary
    functions, or functions expecting a tuple as argument.

    For simplicity, we here follow the approach based on curried
    function, specialized for arity 2 and 3. It is possible to state
    arity-generic definitions and lemmas, but the definitions become
    much more technical.

    From an engineering point of view, it is easier and more efficient
    to follow the approach using n-ary functions, as the CFML tool does. *)

(* ----------------------------------------------------------------- *)
(** *** Syntax for Functions of 2 or 3 Arguments. *)

Notation "'fun' x1 x2 '=>' t" :=
  (val_fun x1 (trm_fun x2 t))
  (in custom trm at level 69,
    x1, x2 at level 0,
    format "'fun'  x1  x2  '=>'  t") : val_scope.

Notation "'fix' f x1 x2 '=>' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (in custom trm at level 69,
    f, x1, x2 at level 0,
    format "'fix'  f  x1  x2  '=>'  t") : val_scope.

Notation "'fun_' x1 x2 '=>' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (in custom trm at level 69,
    x1, x2 at level 0,
    format "'fun_'  x1  x2  '=>'  t") : trm_scope.

Notation "'fix_' f x1 x2 '=>' t" :=
  (trm_fix f x1 (trm_fun x2 t))
  (in custom trm at level 69,
    f, x1, x2 at level 0,
    format "'fix_'  f  x1  x2  '=>'  t") : trm_scope.

Notation "'fun' x1 x2 x3 '=>' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
    x1, x2, x3 at level 0,
    format "'fun'  x1  x2  x3  '=>'  t") : val_scope.

Notation "'fun' x1 x2 x3 x4 '=>' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 t))))
  (in custom trm at level 69,
    x1, x2, x3, x4 at level 0,
    format "'fun'  x1  x2  x3  x4  '=>'  t") : val_scope.

Notation "'fun' x1 x2 x3 x4 x5 '=>' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 (trm_fun x5 t)))))
  (in custom trm at level 69,
    x1, x2, x3, x4, x5 at level 0,
    format "'fun'  x1  x2  x3  x4  x5  '=>'  t") : val_scope.

  (* Notation "'fun' x1 x2 x3 x4 x5 x6 '=>' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 (trm_fun x5 (trm_fun x6 t))))))
  (in custom trm at level 69,
    x1, x2, x3, x5, x6 at level 0,
    format "'fun'  x1  x2  x3  x4  x5  x6  '=>'  t") : val_scope. *)

Notation "'fix' f x1 x2 x3 '=>' t" :=
  (val_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
    f, x1, x2, x3 at level 0,
    format "'fix'  f  x1  x2  x3  '=>'  t") : val_scope.

Notation "'fun_' x1 x2 x3 '=>' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
    x1, x2, x3 at level 0, format "'fun_'  x1  x2  x3  '=>'  t") : trm_scope.

Notation "'fun_' x1 x2 x3 x4 '=>' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 t))))
  (in custom trm at level 69,
    x1, x2, x3, x4 at level 0, format "'fun_'  x1  x2  x3  x4  '=>'  t") : trm_scope.

Notation "'fun_' x1 x2 x3 x4 x5 '=>' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 (trm_fun x4 (trm_fun x5 t)))))
  (in custom trm at level 69,
    x1, x2, x3, x4, x5 at level 0,
    format "'fun_'  x1  x2  x3  x4  x5  '=>'  t") : val_scope.

Notation "'fix_' f x1 x2 x3 '=>' t" :=
  (trm_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
    f, x1, x2, x3 at level 0, format "'fix_'  f  x1  x2  x3  '=>'  t") : trm_scope.

(* ----------------------------------------------------------------- *)
(** *** Evaluation Rules for Applications to 2 or 3 Arguments. *)

(** [eval_like] judgment for applications to several arguments. *)

Lemma eval_like_app_fun2 {D:Type} : forall fs (x1 x2 : D -> var) (t1 : D -> trm) (v1 v2 : D -> val),
  (forall d, indom fs d -> x1 d <> x2 d) ->
  eval_like fs 
    (fun d => (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d))))
    (fun d => (val_fun (x1 d) (trm_fun (x2 d) (t1 d))) (v1 d) (v2 d)).
Proof using.
  introv E N. unfolds eval. destruct N as (H1 & H2). split.
  { introv Hin. applys* eval1_app_args.
    { applys eval1_app_fun. 1: reflexivity. applys eval1_fun. }
    { applys* eval1_val. }
    { applys* eval1_app_fun. case_var. 1: specializes E Hin; eqsolve. by apply H1. }
  }
  { auto. }
Qed.

Lemma eval_like_app_fun3 {D:Type} : forall fs (x1 x2 x3 : D -> var) (t1 : D -> trm) (v1 v2 v3 : D -> val),
  (forall d, indom fs d -> x1 d <> x2 d) ->
  (forall d, indom fs d -> x2 d <> x3 d) ->
  (forall d, indom fs d -> x1 d <> x3 d) ->
  eval_like fs 
    (fun d => (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d)))))
    (fun d => (val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t1 d)))) (v1 d) (v2 d) (v3 d)).
Proof using.
  introv N1 N2 N3 H. unfolds eval. destruct H as (H1 & H2). split.
  { introv Hin. applys* eval1_app_args.
    { applys* eval1_app_args.
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. 
        case_var. 1: specializes N1 Hin; eqsolve.
        case_var. 1: specializes N3 Hin; eqsolve. 
        applys eval1_fun.
      }
      { applys* eval1_val. }
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. 
        case_var. 1: specializes N2 Hin; eqsolve. 
        applys eval1_fun.
      }
    }
    { applys* eval1_val. }
    { applys* eval1_app_fun. }
  }
  { auto. }
Qed.

Lemma eval_like_app_fun4 {D:Type} : forall fs (x1 x2 x3 x4 : D -> var) (t1 : D -> trm) (v1 v2 v3 v4 : D -> val),
  (forall d, indom fs d -> 
    ~ eq (x1 d) (x2 d) /\ 
    ~ eq (x1 d) (x3 d) /\ 
    ~ eq (x1 d) (x4 d) /\ 
    ~ eq (x2 d) (x3 d) /\ 
    ~ eq (x2 d) (x4 d) /\ 
    ~ eq (x3 d) (x4 d)) ->
  eval_like fs 
    (fun d => (subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d))))))
    (fun d => (val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (t1 d))))) (v1 d) (v2 d) (v3 d) (v4 d)).
Proof using.
  introv N H. unfolds eval. destruct H as (H1 & H2). split; auto.
  introv Hin. applys* eval1_app_args.
  { applys* eval1_app_args.
    { applys* eval1_app_args.
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. specializes N Hin. repeat (case_var; try eqsolve).
        applys eval1_fun. }
      { applys* eval1_val. }
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. specializes N Hin. repeat (case_var; try eqsolve).
        applys eval1_fun. } }
    { applys* eval1_val. }
    { applys eval1_app_fun. 1: reflexivity. 
      simpl. specializes N Hin. repeat (case_var; try eqsolve).
      applys eval1_fun. } }
  { applys* eval1_val. }
  { applys* eval1_app_fun. }
Qed.

Lemma eval_like_app_fun5 {D:Type} : forall fs (x1 x2 x3 x4 x5 : D -> var) (t1 : D -> trm) (v1 v2 v3 v4 v5 : D -> val),
  (forall d, indom fs d -> 
      ~ eq (x1 d) (x2 d) /\
      ~ eq (x1 d) (x3 d) /\
      ~ eq (x1 d) (x4 d) /\
      ~ eq (x1 d) (x5 d) /\
      ~ eq (x2 d) (x3 d) /\
      ~ eq (x2 d) (x4 d) /\
      ~ eq (x2 d) (x5 d) /\
      ~ eq (x3 d) (x4 d) /\
      ~ eq (x3 d) (x5 d) /\
      ~ eq (x4 d) (x5 d)) ->
  eval_like fs 
    (fun d => (subst (x5 d) (v5 d) (subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d)))))))
    (fun d => (val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (trm_fun (x5 d) (t1 d)))))) (v1 d) (v2 d) (v3 d) (v4 d) (v5 d)).
Proof using.
  introv N H. unfolds eval. destruct H as (H1 & H2). split; auto.
  introv Hin. applys* eval1_app_args.
  { applys* eval1_app_args.
    { applys* eval1_app_args.
      { applys* eval1_app_args.
        { applys eval1_app_fun. 1: reflexivity. 
          simpl. specializes N Hin. repeat (case_var; try eqsolve).
          applys eval1_fun. }
        { applys* eval1_val. }
        { applys eval1_app_fun. 1: reflexivity. 
          simpl. specializes N Hin. repeat (case_var; try eqsolve).
          applys eval1_fun. } }
      { applys* eval1_val. }
      { applys eval1_app_fun. 1: reflexivity. 
        simpl. specializes N Hin. repeat (case_var; try eqsolve).
        applys eval1_fun. } }
    { applys* eval1_val. }
    { applys eval1_app_fun. 1: reflexivity. 
      simpl. specializes N Hin. repeat (case_var; try eqsolve).
      applys eval1_fun. } }
  { applys* eval1_val. }
  { applys* eval1_app_fun. }
Qed.
(* ----------------------------------------------------------------- *)
(** *** Reasoning Rules for Applications to 2 or 3 Arguments *)

(** Weakest preconditions for applications to several arguments. *)

Lemma wp_app_fun2 {D:Type} fs : forall x1 x2 v0 v1 (v2 : D -> val) t1 Q,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (t1 d))) ->
  (forall d, x1 d <> x2 d) ->
  wp fs (fun (d : D) => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d))) Q ==> wp fs (fun d => trm_app (v0 d) (v1 d) (v2 d)) Q.
Proof using. 
  introv EQ1 N. applys @wp_eval_like. 
  rewrite EQ1.
  by apply eval_like_app_fun2. 
Qed.

Lemma wp_app_fun3 {D:Type} fs : forall v0 (v1 : D -> val) v2 v3 x1 x2 x3 t Q,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (x1 d) (x3 d) = false /\ var_eq (x2 d) (x3 d) = false) ->
  wp fs (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q ==>
  wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) Q.
Proof using.
  introv EQ1 N. applys @wp_eval_like. 
  rewrite EQ1.
  apply eval_like_app_fun3.
  all: intros d ?; rewrite -isTrue_eq_false_eq -var_eq_spec; apply N.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Generalization of [xwp] to Handle Functions of Two Arguments *)

(** Generalization of [xwp] to handle functions of arity 2 and 3,
    and to handle weakening of an existing specification. *)

Lemma xwp_lemma_fun2 {D:Type} : forall v0 v1 (v2 : D -> _) x1 x2 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (t d))) ->
  (forall d, var_eq (x1 d) (x2 d) = false) ->
  H ==> wpgen fs (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d)) H Q.
Proof using.
  introv E M1 M2. rewrite <- wp_equiv. xchange M2.
  set (w := @wpgen_sound D).
  xchange (>> w (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))) Q).
  applys* @wp_app_fun2=> d. 
  by move: (M1 d); rewrite var_eq_spec isTrue_eq_false_eq.
Qed.


Lemma xwp_lemma_wp_fun2 {D:Type} : forall v0 v1 (v2 : D -> _) x1 x2 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (t d))) ->
  (forall d, var_eq (x1 d) (x2 d) = false) ->
  H ==> wpgen fs (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d)) Q.
Proof using.
  introv E M1 M2. eapply himpl_trans. 1: apply M2.
  eapply himpl_trans. 2: apply wp_app_fun2; eauto. 2: intros d; rewrite -isTrue_eq_false_eq -var_eq_spec; apply M1.
  by apply wpgen_sound.
Qed.

Lemma xwp_lemma_fun3 {D:Type} : forall v0 (v1 : D -> val) v2 v3 x1 x2 x3 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (x1 d) (x3 d) = false /\ var_eq (x2 d) (x3 d) = false) ->
  H ==> wpgen fs (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) H Q.
Proof using.
  introv E M1 M2. rewrite <- wp_equiv. xchange M2.
  set (w := @wpgen_sound D).
  xchange (>> w (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q).
  applys* @wp_app_fun3.
Qed.

Lemma xwp_lemma_fun4 {D:Type} : forall v0 v1 (v2 : D -> _) v3 v4 x1 x2 x3 x4 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (t d))))) ->
  (forall d, 
    var_eq (x1 d) (x2 d) = false /\ 
    var_eq (x1 d) (x3 d) = false /\ 
    var_eq (x1 d) (x4 d) = false /\ 
    var_eq (x2 d) (x3 d) = false /\ 
    var_eq (x2 d) (x4 d) = false /\ 
    var_eq (x3 d) (x4 d) = false
    ) ->
  H ==> wpgen fs (fun d => subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d) (v4 d)) H Q.
Proof using.
  introv E M1 M2. rewrite <- wp_equiv. xchange M2.
  set (w := @wpgen_sound D).
  xchange (>> w (fun d => subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))))) Q).
  applys @wp_eval_like. 
  rewrite E.
  apply eval_like_app_fun4.
  all: intros d ?; rewrite -?isTrue_eq_false_eq -?var_eq_spec; apply M1.
Qed.

Lemma xwp_lemma_fun5 {D:Type} : forall v0 v1 (v2 : D -> _) v3 v4 v5 x1 x2 x3 x4 x5 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (trm_fun (x5 d) (t d)))))) ->
  (forall d, 
    var_eq (x1 d) (x2 d) = false /\ 
    var_eq (x1 d) (x3 d) = false /\ 
    var_eq (x1 d) (x4 d) = false /\ 
    var_eq (x1 d) (x5 d) = false /\ 
    var_eq (x2 d) (x3 d) = false /\ 
    var_eq (x2 d) (x4 d) = false /\ 
    var_eq (x2 d) (x5 d) = false /\ 
    var_eq (x3 d) (x4 d) = false /\
    var_eq (x3 d) (x5 d) = false /\ 
    var_eq (x4 d) (x5 d) = false
    ) ->
  H ==> wpgen fs (fun d => 
    subst (x5 d) (v5 d) (
      subst (x4 d) (v4 d) (
        subst (x3 d) (v3 d) (
          subst (x2 d) (v2 d) (
            subst (x1 d) (v1 d) 
            (t d)))))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d) (v4 d) (v5 d)) H Q.
Proof using.
  introv E M1 M2. rewrite <- wp_equiv. xchange M2.
  set (w := @wpgen_sound D).
  xchange (>> w (fun d => subst (x5 d) (v5 d) (subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))))) Q).
  applys @wp_eval_like. 
  rewrite E.
  apply eval_like_app_fun5.
  all: intros d ?; rewrite -?isTrue_eq_false_eq -?var_eq_spec; apply M1.
Qed.

Lemma xwp_lemma_wp_fun3{D:Type}  : forall v0 v1 v2 (v3 : D -> _) x1 x2 x3 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (x1 d) (x3 d) = false /\ var_eq (x2 d) (x3 d) = false) ->
  H ==> wpgen fs (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) Q.
Proof using. introv E M1 M2. eapply wp_equiv, xwp_lemma_fun3; eauto. Qed.

Lemma xwp_lemma_wp_fun4 {D:Type} : forall v0 v1 v2 (v3 : D -> _) v4 x1 x2 x3 x4 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (t d))))) ->
  (forall d, 
    var_eq (x1 d) (x2 d) = false /\ 
    var_eq (x1 d) (x3 d) = false /\ 
    var_eq (x1 d) (x4 d) = false /\ 
    var_eq (x2 d) (x3 d) = false /\ 
    var_eq (x2 d) (x4 d) = false /\ 
    var_eq (x3 d) (x4 d) = false
    ) ->
  H ==> wpgen fs (fun d => subst (x4 d) (v4 d) (subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d) (v4 d)) Q.
Proof using. introv E M1 M2. eapply wp_equiv, xwp_lemma_fun4; eauto. Qed.

Lemma xwp_lemma_wp_fun5 {D:Type} : forall (v0 : D -> _) v1 v2 v3 v4 v5 x1 x2 x3 x4 x5 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (trm_fun (x4 d) (trm_fun (x5 d) (t d)))))) ->
  (forall d, 
    var_eq (x1 d) (x2 d) = false /\ 
    var_eq (x1 d) (x3 d) = false /\ 
    var_eq (x1 d) (x4 d) = false /\ 
    var_eq (x1 d) (x5 d) = false /\ 
    var_eq (x2 d) (x3 d) = false /\ 
    var_eq (x2 d) (x4 d) = false /\ 
    var_eq (x2 d) (x5 d) = false /\ 
    var_eq (x3 d) (x4 d) = false /\
    var_eq (x3 d) (x5 d) = false /\ 
    var_eq (x4 d) (x5 d) = false
    ) ->
  H ==> wpgen fs (fun d => 
    subst (x5 d) (v5 d) (
      subst (x4 d) (v4 d) (
        subst (x3 d) (v3 d) (
          subst (x2 d) (v2 d) (
            subst (x1 d) (v1 d) 
            (t d)))))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d) (v4 d) (v5 d)) Q.
Proof using. introv E M1 M2. eapply wp_equiv, xwp_lemma_fun5; eauto. Qed.

Tactic Notation "xwp" :=
  intros;
  first [ applys @xwp_lemma_fun;     [ reflexivity | ]
        | applys @xwp_lemma_wp_fun;  [ reflexivity | ]
        | applys @xwp_lemma_fix;     [ reflexivity | ]
        | applys @xwp_lemma_fix';    [ reflexivity | ]
        | applys @xwp_lemma_wp_fix'; [ reflexivity | ]
        | applys @xwp_lemma_wp_fix;  [ reflexivity | ]
        | applys @xwp_lemma_fun2;    [ reflexivity | reflexivity | ]
        | applys @xwp_lemma_wp_fun2; [ reflexivity | reflexivity | ]
        | applys @xwp_lemma_fun3;    [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_wp_fun3; [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_fun4;    [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_wp_fun4; [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_fun5;    [ reflexivity | (do ? split); reflexivity | ]
        | applys @xwp_lemma_wp_fun5; [ reflexivity | (do ? split); reflexivity | ]
        (* | applys xwp_lemma_wp_fix3; [ reflexivity | (do ? split); reflexivity | ] *)
        | applys @wp_of_wpgen
        | fail 1 "xwp only applies to functions defined using [val_fun] or [val_fix], with at most 3 arguments" ];
  xwp_simpl.

Section For_loop.

Context {Dom : Type}.

Import ProgramSyntax.

Definition For_aux (N : trm) (body : trm) : trm :=
  trm_fix "for" "cnt"
    <{ let "cond" = ("cnt" < N) in 
      if "cond" then 
        let "body" = body in
        "body" "cnt";
        let "cnt" = "cnt" + 1 in 
        "for" "cnt"
      else 0 }>.

Definition While_aux (cond : trm) (body : trm) : trm :=
  trm_fix "while" "tt"
    <{ let "cond" = cond in 
      if "cond" then 
          body;
        "while" "tt"
      else 0 }>.

Definition For_aux' (N : trm) (body : trm) : trm :=
  val_fix "for" "cnt"
    <{ let "cond" = ("cnt" < N) in 
      if "cond" then 
        let "body" = body in
        "body" "cnt";
        let "cnt" = "cnt" + 1 in 
        "for" "cnt"
      else 0 }>.

Definition For (Z : trm) (N : trm) (body : trm) : trm :=
  let f := For_aux N body in <{ f Z }>.

Definition While (cond : trm) (body : trm) : trm :=
  let f := While_aux cond body in <{ f 0 }>.

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Lemma label_union {T : Type} (fs1 fs2 : fset T) l : 
  label (Lab l (fs1 \u fs2)) = label (Lab l fs1) \u label (Lab l fs2).
Proof using.
  elim/fset_ind: fs1=> [|fs x IHfs ?] in fs2 *.
  { by rewrite label_empty ?union_empty_l. }
  by rewrite -update_union_not_r' ?label_update IHfs update_union_not_r'.
Qed.

Lemma Union_label {T D} (fs : fset T) l  (fsi : T -> fset D) :
  label (Lab l (Union fs fsi)) = Union fs (fun t => label (Lab l (fsi t))).
Proof.
  elim/fset_ind: fs.
  { by rewrite ?Union0 label_empty. }
  move=> fs x IHfs ?.
  by rewrite ?Union_upd_fset label_union IHfs.
Qed.

Fact interval_fsubst_offset (L R offset : int) :
  fsubst (interval L R) (fun i => i + offset) = 
  interval (L + offset) (R + offset).
Proof.
  apply fset_extens. intros.
  rewrite indom_fsubst. setoid_rewrite indom_interval.
  split.
  { intros (? & <- & ?). lia. }
  { intros. exists (x-offset). lia. }
Qed.

Hint Resolve eqbxx : lhtriple.

Context `{HD : Inhab Dom}.

Lemma htriple_sequ1 (fs fs' : fset Dom) H H' Q ht ht1 ht2 htsuf ht'
  (Hdj : disjoint fs fs')
  (Htp1 : htriple fs ht1 H (fun=> H'))
  (Hhtsuf : forall d, indom fs d -> htsuf d = ht2 d)
  (Hhtsuf' : forall d, indom fs' d -> htsuf d = ht' d)
  (Htpsuf : htriple (fs \u fs') htsuf H' Q)
  (Hht : forall d, indom fs d -> ht d = trm_seq (ht1 d) (ht2 d))
  (Hht' : forall d, indom fs' d -> ht d = ht' d) :
  htriple (fs \u fs') ht H Q.
Proof.
  apply wp_equiv.
  rewrite <- wp_union; auto.
  rewrite -> wp_ht_eq with (ht1:=ht) (ht2:=fun d => trm_seq (ht1 d) (ht2 d)); auto.
  xwp. xseq.
  apply wp_equiv.
  eapply htriple_conseq.
  1: apply Htp1.
  1: xsimpl.
  1:{ 
    xsimpl. 
    rewrite -> wp_ht_eq with (ht1:=ht2) (ht2:=htsuf).
    2: intros; by rewrite -> Hhtsuf.
    eapply himpl_trans. 
    2: apply wp_conseq with (Q1:=fun v => wp fs' htsuf 
      (fun hr2 : Dom -> val => Q ((v \u_ fs) hr2))).
    2:{ 
      hnf. intros. 
      rewrite -> wp_ht_eq with (ht1:=ht) (ht2:=htsuf); auto.
      intros. rewrite -> Hht'; auto. rewrite -> Hhtsuf'; auto.
    }
    rewrite -> wp_union; auto.
    by apply wp_equiv.
  }
Qed.

Lemma htriple_sequ2 (fs fs' : fset Dom) H Q' Q ht ht1 ht2 htpre ht'
  (Hdj : disjoint fs fs')
  (Hhtpre : forall d, indom fs d -> htpre d = ht1 d)
  (Hhtpre' : forall d, indom fs' d -> htpre d = ht' d)
  (Htppre : htriple (fs \u fs') htpre H Q') (* hv? *)
  (Hht : forall d, indom fs d -> ht d = trm_seq (ht1 d) (ht2 d))
  (Hht' : forall d, indom fs' d -> ht d = ht' d)
  (Htp2 : forall hv, htriple fs ht2 (Q' hv) (fun hr => Q (uni fs' hv hr))) :
  htriple (fs \u fs') ht H Q.
Proof using.
  apply wp_equiv.
  rewrite -> union_comm_of_disjoint. 2: apply Hdj.
  rewrite <- wp_union. 2: rewrite -> disjoint_comm; apply Hdj.
  rewrite -> wp_ht_eq with (ht2:=ht').
  2: apply Hht'.
  rewrite -> wp_ht_eq with (ht2:=htpre).
  2: introv HH; rewrite -> Hhtpre'; try reflexivity; try apply HH.
  apply wp_equiv.

  eapply htriple_conseq.
  3:{ 
    hnf. intros v. 
    eapply himpl_trans.
    1: apply wp_seq.
    rewrite -> wp_ht_eq with (ht1:=ht) (ht2:=fun d => trm_seq (ht1 d) (ht2 d)).
    2: apply Hht.
    apply himpl_refl.
  }
  1:{ 
    apply wp_equiv.
    eapply wp_conseq. hnf. intros.
    match goal with |- himpl _ (wp ?fs _ ?ff) => 
      eapply himpl_trans with (H2:=wp fs htpre ff) end.
    1: apply himpl_refl.
    rewrite -> wp_ht_eq with (ht1:=ht1) (ht2:=htpre).
    2: introv HH; rewrite -> Hhtpre; try reflexivity; try apply HH.
    apply himpl_refl.
  }
  apply wp_equiv in Htppre.
  rewrite -> union_comm_of_disjoint in Htppre. 2: apply Hdj.
  rewrite <- wp_union in Htppre. 2: rewrite -> disjoint_comm; apply Hdj.
  eapply himpl_trans.
  1: apply Htppre.
  apply wp_conseq.
  hnf. intros. apply wp_conseq.
  hnf. intros. 
  xapp=> hv.
  move=> ?; apply:applys_eq_init; f_equal; extens=> ?; rewrite /uni.
  do? case:classicT=> //.
Qed.

Lemma wp_for_aux  i fs fs' ht (H : int -> (Dom -> val) -> hhprop Dom) (Z N : int) C fsi hv0 vr:
  (Z <= i <= N) ->
  (forall j hv1 hv2, i <= j <= N -> (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> H j hv1 = H j hv2) ->
  (forall i j, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi i) (fsi j)) ->
  fs = Union (interval i N) fsi ->
  (forall t, subst "for" t C = C) ->
  (forall t, subst "cnt" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  disjoint fs' fs ->
  (forall x, indom fs' x -> ht x = For i N (trm_fun vr C)) ->
  (forall j hv, Z <= j < N -> H j hv ==> 
    wp
      (fs' \u fsi j) 
      ((fun=> subst vr j C) \u_fs' ht) 
      (fun hr => H (j + 1) (hv \u_(Union (interval Z j) fsi) hr))) ->
  H i hv0 ==> 
    wp
      (fs' \u fs)
      ht 
      (fun hr => H N (hv0 \u_(Union (interval Z i) fsi) hr)).
Proof. 
  move=> + hP Dj -> sfor scnt scond vcnt vfor vcond  + +.
  move: ht hv0 hP.
  induction_wf IH: (upto N) i; rewrite /upto le_zarith lt_zarith in IH.
  move=> ht hv0 hP lN dj htE.
  rewrite -wp_union // (wp_ht_eq _ _ _ htE) /For /For_aux.
  rewrite wp_fix_app2.
  Opaque subst.
  xwp.
  Transparent subst. 
  rewrite vcnt vfor sfor /=.
  xapp; rewrite vcond scnt scond.
  xwp; xif.
  { move=> ?. xwp; xlet.
    apply:himpl_trans; first last.
    { apply: wp_fun. }
    simpl; xwp. xseq.
    Opaque subst.
    apply: himpl_trans; first last.
    { apply wp_app_fun=> ?. reflexivity. }
    simpl; remember (subst vr i C) as sub eqn:subE.
    Transparent subst.
    apply: himpl_trans; first last.
    { apply/wp_conseq=> ?. xwp. xlet. xapp. }
    apply: himpl_trans; first last.
    { apply/wp_conseq=> ?. 
      rewrite hstar_hempty_l. 
      apply himpl_qwand_r=> ?. rewrite /protect. 
      xsimpl=>->.
      rewrite -wp_fix_app2.
      set (ht' := (fun=> For_aux N (trm_fun vr C) (i + 1)) \u_fs' ht).
      rewrite (wp_ht_eq _ ht').
      { apply/wp_conseq=> ?; rewrite (wp_ht_eq _ ht'). xsimpl*.
        by move=> ? IND; rewrite /ht' uni_nin // => /(disjoint_inv_not_indom_both dj). }
        by move=> ??; rewrite /ht' uni_in. }
    rewrite (wp_union (fun hr2 => H N (_ \u_ _ hr2))) //.
    rewrite // intervalU; last lia. 
    rewrite // Union_upd // -?union_assoc; first last.
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; lia. }
      move=> ? [?|?]; subst; apply/Dj; lia. }
    rewrite union_comm_of_disjoint -?union_assoc; first rewrite union_comm_of_disjoint.
    2-3: move: dj; rewrite disjoint_union_eq_l ?disjoint_Union.
    2-3: setoid_rewrite indom_interval=> dj; do ?split.
    2-5: by intros; (apply/dj; lia) + (apply/Dj; lia).
    rewrite -wp_union; first last.
    { move: dj; rewrite disjoint_union_eq_r ?disjoint_Union.
      setoid_rewrite indom_interval=> dj; split=> *; [apply/Dj|apply/dj]; lia. }
    set (ht' := (fun=> subst vr i C) \u_fs' ht).
    rewrite (wp_ht_eq _ ht'); first last.
    { by move=> *; rewrite subE /ht' uni_in. }
    rewrite (wp_ht_eq (_ \u_ _ _) ht'); first last.
    { move=> ??; rewrite /ht' ?uni_nin // => /(@disjoint_inv_not_indom_both _ _ _ _ _); apply; eauto.
      all: rewrite indom_Union; setoid_rewrite indom_interval; do? eexists;eauto; lia. }
    apply: himpl_trans; last apply/wp_union2; first last.
    { move: dj; rewrite disjoint_Union disjoint_comm; apply.
      rewrite indom_interval; lia. }
    have: (Z <= i < N) by lia.
    move: (H0 i hv0)=> /[apply]/wp_equiv S; xapp S.
    move=> hr.
    apply: himpl_trans; first last.
    { apply: wp_conseq=> ?; rewrite uniA=> ?; exact. }
    set (hv0 \u_ _ _); rewrite [_ \u fsi i]union_comm_of_disjoint; first last.
    { rewrite disjoint_Union.
      setoid_rewrite indom_interval=> *; apply/Dj; lia. }
    rewrite -Union_upd // -intervalUr; try lia.
    rewrite union_comm_of_disjoint; first last.
    { move: dj; rewrite ?disjoint_Union; setoid_rewrite indom_interval.
      move=> dj *; apply/dj; lia. }
    apply IH; try lia.
    { move=> *; apply/hP; eauto; lia. }
    { move: dj; rewrite ?disjoint_Union; setoid_rewrite indom_interval.
      move=> dj *; apply/dj; lia. }
    { by move=> *; rewrite uni_in. }
    move=> j ??.
    rewrite (wp_ht_eq _ ((fun=> (subst vr j C)) \u_ fs' ht)); eauto.
    move=> ??; rewrite /uni. case: classicT=> //.
    move=> ???; rewrite ?indom_interval=> ??.
    apply/Dj; lia. }
    move=> ?; have->: i = N by lia.
    xwp; xval.
    rewrite intervalgt ?Union0; last lia.
    rewrite wp0_dep. xsimpl hv0.
    erewrite hP; eauto. lia.
    by move=> ??; rewrite uni_in. 
Qed.

Lemma upd_upd_eq {A B} (f : A -> B) x y y' : 
  upd (upd f x y) x y' = upd f x y'.
Proof. by extens=> ?; rewrite /upd; do ? case: classicT. Qed.

Lemma wp_while_aux i fs fs' ht (H : bool -> int -> (Dom -> val) -> hhprop Dom) (Z N : int) T C fsi s b0 hv0 :
  (forall j b hv1 hv2, (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> H b j hv1 = H b j hv2) ->
  fs = Union (interval i N) fsi ->
  fs' = single s tt ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (forall j, (i <= j < N) -> ~ indom (fsi j) s) ->
  (Z <= i <= N) ->
  (ht s = While C T) ->
  (forall (b : bool) (x : int) hv,
    H b x hv ==>
      wp 
        fs'
        (fun=> C) 
        (fun hc => \[hc s = b] \* H b x hv)) -> 
  (forall x hv, H false x hv ==> \[(x = N)] \* H false x hv) ->
  (forall x hv, H true x hv ==> \[(x < N)] \* H true x hv) ->
  (forall j hv, Z <= j < N ->
    (forall j' b' hv, 
        htriple (fs' \u Union (interval j' N) fsi)
          (upd ht s (While C T)) 
          (H b' j' hv \* \[j < j' <= N])
          (fun hr => H false N (hv \u_(Union (interval Z j') fsi) hr))) ->
    H true j hv ==> 
      wp
        (fs' \u Union (interval j N) fsi) 
        (upd ht s (trm_seq T (While C T))) 
        (fun hr => H false N (hv \u_(Union (interval Z j) fsi) hr))) ->
  H b0 i hv0 ==> 
    wp
      (fs' \u fs)
      ht 
      (fun hr => H false N (hv0 \u_(Union (interval Z i) fsi) hr)).
Proof with autos*.
  move=> HE ->-> swhile scond stt cw cc ct +++ HCi IHf HCi'.
  move: ht hv0 b0. induction_wf IH: (upto N) i; rewrite /upto le_zarith lt_zarith in IH.
  move=> ht hv0 b Dj' ? htsE IHt.
  have htE: forall x, indom (single s tt) x -> ht x = While C T.
  { by move=> ? /[! @indom_single_eq]<-. }
  have?: disjoint (single s tt) (Union (interval i N) fsi).
  { rewrite disjoint_Union=> ?/[! @indom_interval]?.
    rewrite disjoint_comm.
    apply/disjoint_single_of_not_indom/Dj'; lia. }
  rewrite -wp_union // (wp_ht_eq _ _ _ htE) /While /While_aux. 
  rewrite wp_fix_app2.
  Opaque subst.
  xwp.
  Transparent subst.
  rewrite /= cw swhile stt ct.
  xlet.
  move=> ? /HCi; apply/wp_conseq=> hv.
  xpull; case:b => -hvsE.
  { under wp_ht_eq.
    { move=> ? /[! indom_single_eq]<-/[! hvsE] /[! over] //. }
    rewrite -/(himpl _ _).
    Opaque subst.
    xwp.
    Transparent subst.
    xif=> // _.
    rewrite scond. rewrite -/(While_aux _ _).
    rewrite -wp_fix_appapp2 -/(While_aux _ _)-/(While _ _).
    under wp_ht_eq; rewrite -/(himpl _ _).
    { move=> s' /[! indom_single_eq] sE.
      rewrite -(upd_eq _ _ ht s (trm_seq T (While C T))) {2}sE over //. }
    rewrite wp_equiv.
    apply/htriple_conseq; first last; [|clear HCi; eauto|].
    { move=> ?. under wp_ht_eq; rewrite -/(himpl _ _).
      { move=> s'; rewrite indom_Union=> -[?][].
        rewrite indom_interval => /Dj' ??.
        rewrite -(upd_neq _ _ ht s (trm_seq T (While C T))) ?over //.
        move=> ?. by subst. } 
      move=> ?; exact. }
    rewrite -wp_equiv (wp_union (fun hv => H false N (_ \u_ _ hv))) //.
    xpull=> ?.
    apply/IHt; first by lia.
    move=> j' b' ?; apply wp_equiv; xsimpl=> ?.
    apply/IH; try lia.
    { move=> ??; apply/Dj'; lia. }
    { by rewrite upd_eq. }
    move=> > ?.
    rewrite ?upd_upd_eq; exact/IHt. }
  under wp_ht_eq.
  { move=> ? /[! indom_single_eq]<-/[! hvsE] /[! over] //. }
  rewrite -/(himpl _ _).
  xwp; xif=> // _.
  xwp; xval; apply:himpl_trans; [exact/IHf|].
  xsimpl=> ->; rewrite intervalgt ?Union0 ?wp0_dep; last lia.
  by xsimpl hv0; erewrite HE; eauto=> ??; rewrite uni_in.
Qed.

Lemma wp_while_aux_unary i fs' (H : bool -> int -> hhprop Dom) Z N T C s b0 :
  fs' = single s tt ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (Z <= i <= N) ->
  (forall (b : bool) (x : int),
    H b x ==>
      wp 
        fs'
        (fun=> C) 
        (fun hc => \[hc s = b] \* H b x)) -> 
  (forall x, H false x ==> \[(x = N)] \* H false x) ->
  (forall x, H true x ==> \[(x < N)] \* H true x) ->
  (forall j, Z <= j < N ->
    (forall j' b', 
      htriple fs'
        (fun=> While C T)
        (H b' j' \* \[j < j' <= N])
        (fun=> H false N)) ->
    H true j ==> wp fs' (fun=> (trm_seq T (While C T))) (fun=> H false N)) ->
  H b0 i ==> wp fs' (fun=> While C T) (fun=> H false N).
Proof with autos*.
  move=>-> ?????? ? HC Hf HC' IH.
  apply: himpl_trans.
  { apply/(@wp_while_aux i empty (single s tt) (fun=> While C T) (fun b x hv => H b x) _ _ T _ (fun=> empty)); eauto.
    { exact/(fun=> val_unit). }
    { by rewrite UnionN0. }
    move=> ? _ {}/IH IH IH'.
    rewrite UnionN0 union_empty_r.
    rewrite (wp_ht_eq _ (fun=> trm_seq T (While C T))).
    { apply/IH=> j' b.
      move: (IH' j' b (fun=> val_unit)); rewrite -?wp_equiv=> {}IH' ? /IH'.
      rewrite UnionN0 (wp_ht_eq _ (fun=> While C T)) ?union_empty_r //.
      by move=> ?; rewrite indom_single_eq=>->; rewrite upd_eq. }
    by move=> ?; rewrite indom_single_eq=>->; rewrite upd_eq. }
  by rewrite UnionN0 union_empty_r.
Qed.

Lemma wp_for fs fs' ht 
  (H : int -> (Dom -> val) -> hhprop Dom) Z N (C : trm) fsi hv0 (P : hhprop Dom) Q vr :
  (forall j hv, Z <= j < N -> H j hv ==> wp (fs' \u fsi j) ((fun=> subst vr j C) \u_fs' ht) (fun hr => H (j + 1) (hr \u_(fsi j) hv))) ->
  (forall j hv1 hv2, Z <= j <= N -> (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> H j hv1 = H j hv2) ->
  (P ==> H Z hv0) -> 
  (H N ===> Q) ->
  (forall i j, i <> j -> Z <= i < N -> Z <= j < N -> disjoint (fsi i) (fsi j)) ->
  (Z <= N) ->
  fs = Union (interval Z N) fsi ->
  (forall t, subst "for" t C = C) ->
  (forall t, subst "cnt" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  disjoint fs' fs ->
  (forall x, indom fs' x -> ht x = For Z N (trm_fun vr C)) ->
  P ==> wp (fs' \u fs) ht Q.
Proof.
  move=> Hwp Heq HP HQ Dj *.
  apply: himpl_trans; first exact/HP.
  apply: himpl_trans; first last.
  { apply: wp_conseq; exact/HQ. }
  apply: himpl_trans.
  { apply/(@wp_for_aux Z); eauto; first lia.
    clear -Hwp Heq Dj=> i hv lP.
    move=> ? // /Hwp -/(_ lP). apply/wp_conseq=> hr.
    erewrite Heq; try lia; eauto=> ?.
    rewrite intervalUr ?Union_upd // ?indom_union_eq; last lia; first last.
    { introv Neq. rewrite ?indom_union_eq ?indom_interval ?indom_single_eq.
      case=> [?[?|]|]; first by subst.
      { subst=> ?; apply/Dj=> //; lia. }
      move=> ? [?|?]; subst; apply/Dj; lia. }
    have ?: disjoint (Union (interval Z i) fsi) (fsi i).
    { apply/disjoint_of_not_indom_both=> ?; rewrite indom_Union.
      case=> ?; rewrite indom_interval=> -[?].
      apply/disjoint_inv_not_indom_both/Dj; lia. }
    case=> IND. 
    { rewrite uni_in // uni_nin //.
      apply/disjoint_inv_not_indom_both; rewrite 1?disjoint_comm; eauto. }
    rewrite uni_nin ?uni_in //.
    apply/disjoint_inv_not_indom_both; eauto. }
  apply/wp_conseq=> ?; rewrite intervalgt ?Union0 ?uni0 //; by lia.
Qed.

Lemma wp_while fs fs' ht (Inv : bool -> int -> (Dom -> val) -> hhprop Dom) Z N T C fsi s b0 hv0 (P : hhprop Dom) Q :
  (forall (b : bool) (x : int) hv,
    Inv b x hv ==>
      wp 
        fs'
        (fun=> C) 
        (fun hc => \[hc s = b] \* Inv b x hv)) -> 
  (forall x hv, Inv false x hv ==> \[(x = N)] \* Inv false x hv) ->
  (forall x hv, Inv true x hv ==> \[(x < N)] \* Inv true x hv) ->
  (forall j hv, Z <= j < N ->
    (forall j' b' hv, 
      htriple (fs' \u Union (interval j' N) fsi)
        (upd ht s (While C T)) 
        (Inv b' j' hv \* \[j < j' <= N])
        (fun hr => Inv false N (hv \u_(Union (interval Z j') fsi) hr))) ->
      Inv true j hv ==> 
        wp
          (fs' \u Union (interval j N) fsi) 
          (upd ht s (trm_seq T (While C T))) 
          (fun hr => Inv false N (hv \u_(Union (interval Z j) fsi) hr))) ->
  (forall j b hv1 hv2, (forall x, indom (Union (interval Z j) fsi) x -> hv1 x = hv2 x) -> Inv b j hv1 = Inv b j hv2) ->
  P ==> Inv b0 Z hv0 ->
  Inv false N ===> Q ->
  (Z <= N) ->
  fs = Union (interval Z N) fsi ->
  fs' = single s tt ->
  (forall t, subst "while" t T = T) ->
  (forall t, subst "cond" t T = T) ->
  (forall t, subst "tt" t T = T) ->
  (forall t, subst "while" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  (forall t, subst "tt" t C = C) ->
  (forall j, (Z <= j < N) -> ~ indom (fsi j) s) ->
  (ht s = While C T) ->
  P ==> wp (fs' \u fs) ht Q.
Proof with autos*.
  move=> HwpC HwpF HwpT HwpT' Heq HP HQ *.
  apply: himpl_trans; first exact/HP.
  apply: himpl_trans; first last.
  { apply: wp_conseq; exact/HQ. }
  apply: himpl_trans.
  { apply/(wp_while_aux (i := Z) (ht := ht) _ (T := T)); eauto. lia. }
  apply/wp_conseq=> ?; rewrite intervalgt ?Union0 ?uni0 //; by lia.
Qed.

Hint Resolve hmerge_comm hmerge_assoc : core.

Lemma wp_for_hbig_op fs fs' ht fs''
  Inv
  (R R' : Dom -> hhprop Dom)
  m vd (H : int -> hhprop Dom) (H' : int -> (Dom -> val) -> hhprop Dom) 
  Z N (C : trm) fsi (P : hhprop Dom) Q vr :
  (forall i, hlocal (H i) fs'') ->
  (forall i v, hlocal (H' i v) fs'') ->
  (forall l Q, Z <= l < N -> 
    hlocal Q fs'' ->
    Inv l \* 
    (\*_(d <- fsi l) R d) \* 
    Q \(m, vd) H l ==> 
      wp (fs' \u fsi l) 
          ((fun=> subst vr l C) \u_fs' ht) 
          (fun hr => 
            Inv (l + 1) \* 
            (\*_(d <- fsi l) R' d) \* 
            Q \(m, vd) H' l hr)) ->
  (forall (hv hv' : Dom -> val) m,
    Z <= m < N ->
    (forall i, indom (fsi m) i -> hv(i) = hv'(i)) ->
    H' m hv = H' m hv') ->
  comm m -> assoc m -> (forall x y, (vd x /\ vd y) <-> vd (m x y)) ->
  (P ==>  
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi) R d) \*
    \(m, vd)_(i <- interval Z N) H i) -> 
  (forall hv,
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi) R' d) \* 
    (\(m, vd)_(i <- interval Z N) H' i hv) ==> Q hv) ->
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  (Z <= N) ->
  fs = Union (interval Z N) fsi ->
  (forall t, subst "for" t C = C) ->
  (forall t, subst "cnt" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  disjoint fs' fs ->
  (forall x, indom fs' x -> ht x = For Z N (trm_fun vr C)) ->
  P ==> wp (fs' \u fs) ht Q.
Proof.
  move=> Hl1 Hl2 Hwp Heq CM AS VM HP HQ Dj *.
  apply: himpl_trans; first exact/HP.
  apply: himpl_trans; first last.
  { apply: wp_conseq; exact/HQ. }
  apply/(wp_for
      (fun q hv => 
        Inv q \* 
        (\*_(d <- Union (interval Z q) fsi) R' d) \*
        (\*_(d <- Union (interval q N) fsi) R d) \* 
        (\(m, vd)_(i <- interval Z q) H' i hv) \(m, vd) (\(m, vd)_(i <- interval q N) H i)) _ (fun=> 0)); eauto.
  { clear -Hwp Dj CM AS Heq Hl1 Hl2 VM.
    move=> l hv ?. 
    set (Q := (\(m, vd)_(i <- interval Z l) H' i hv) \(m, vd) (\(m, vd)_(i <- interval (l + 1) N) H i)).
    move: (Hwp l Q)=> IH.
    rewrite {1}intervalUr ?Union_upd //; last lia; autos*.
    have Dj': disjoint (fsi l) (Union (interval Z l) fsi).
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; lia. }
    rewrite hbig_fset_union // (@intervalU l N); last lia.
    rewrite Union_upd //; autos*; rewrite hbig_fset_union //; first last.
    { rewrite disjoint_Union=> ? /[! indom_interval] ?.
      apply/Dj; lia. }
    apply/xapp_lemma'; [|rewrite <-wp_equiv; apply/IH; try lia|].
    { reflexivity. }
    { rewrite /Q; apply/hlocal_hmerge; exact/hlocal_hmerge_fset. }
    unfold protect.
    rew_heap.
    xsimpl*.
    suff<-: Q \(m, vd) H l = 
      (\(m, vd)_(i0 <- interval Z l) H' i0 hv) \(m, vd) 
      (\(m, vd)_(i0 <- update (interval (l + 1) N) l tt) H i0).
    { xsimpl=> hr. rewrite /Q.
      rewrite hmerge_assoc // [_ \(m, vd) H' _ _]hmerge_comm //.
      rewrite -hmerge_assoc // => h.
      apply: applys_eq_init; apply/(congr1 (@^~ h)).
      fequal. rewrite intervalUr ?hbig_fset_update //; eauto; last lia.
      { rewrite hmerge_comm; eauto. fequal.
        { apply/hbig_fset_eq=> ? +; rewrite indom_interval=> ?. 
          (apply/Heq; try lia)=> ? ind; rewrite uni_nin //.
          move: ind=> /[swap]; apply/disjoint_inv_not_indom_both/Dj; lia. }
        apply/Heq=> *; try lia; by rewrite uni_in. }
      rewrite indom_interval not_and_eq; right. lia. }
      rewrite /Q hmerge_assoc // [_ \(m, vd) H _]hmerge_comm //.
      rewrite hbig_fset_update ?indom_interval; eauto.
      rewrite not_and_eq; left.
      lia. }
  { move=> q hv hv' ? hvE.
    suff->:
      (\(m, vd)_(i0 <- interval Z q) H' i0 hv') = 
      (\(m, vd)_(i0 <- interval Z q) H' i0 hv) by [].
    apply/hbig_fset_eq=> ?; rewrite indom_interval=> ?. 
    apply/Heq=> *; try lia. apply/eq_sym/hvE.
    rewrite indom_Union; eexists; rewrite indom_interval; autos*. }
  { rewrite [_ Z Z]intervalgt; last lia.
    rewrite Union0 ?hbig_fset_empty hmerge_hempty_l; xsimpl. }
  { move=> ?.
    rewrite [_ N N]intervalgt; last lia.
    rewrite Union0 ?hbig_fset_empty hmerge_hempty_r. xsimpl. }
Qed.

Lemma interval_union y x z : 
  x <= y -> 
  y <= z -> interval x y \u interval y z = interval x z.
Proof.
  move=> +?.
  induction_wf IH: (upto y) x; rewrite /upto le_zarith lt_zarith in IH.
  move=> ?.
  case: (prop_inv (x = y))=> [->|?].
  { rewrite intervalgt; rew_fmap=> //; lia. }
  rewrite intervalU -?update_union_not_r' ?IH -?intervalU //; by lia.
Qed.

Arguments interval_union : clear implicits.

Lemma hbig_fset_Union {A : Type} (fs : fset A) fsi (H : A -> hhprop Dom) : 
  (forall i j, i <> j -> indom fs i -> indom fs j -> disjoint (fsi i) (fsi j)) ->
    \*_(i <- Union fs fsi) H i =
    \*_(i <- fs) \*_(d <- fsi i) H d.
Proof.
  elim/fset_ind: fs. 
  { by rewrite Union0 ?hbig_fset_empty. }
  move=> fs x IHfs Hnotin Hdj.
  have?: disjoint (fsi x) (Union fs fsi).
  { rewrite disjoint_Union=> y ?. apply/Hdj; [ by intros -> | | ]; rewrite indom_update_eq; tauto. }
  rewrite Union_upd // hbig_fset_union // hbig_fset_update // IHfs //.
  intros. apply Hdj=> //; rewrite indom_update_eq; tauto.
Qed.

Lemma valid_subst_not_squash h1 h2 (f : Dom -> Dom) fs1 fs2 : 
  valid_subst (h1 \u h2) (fun x : loc * Dom => (x.1, f x.2)) ->
  (forall x y, x <> y -> indom fs1 x -> indom fs2 y -> f x <> f y) ->
  local fs1 h1 ->
  local fs2 h2 ->
    valid_subst h1 (fun x : loc * Dom => (x.1, f x.2)).
Proof.
  move=> v fP l1 l2.
  case=> ? d1[l d2]/= /[dup]-[->]fE ffE.
  move: (v (l, d1) (l, d2) ffE).
  case: (prop_inv (indom h1 (l, d1))).
  { case: (prop_inv (indom h2 (l, d2))).
    { move=> /l2/fP fN /l1/fN/[! fE].
      by case: (classicT (d1 = d2))=> [->//|/[swap]/[apply] ]. }
    move=> ??. by rewrite fmapU_in1 // fmapU_nin2. }
  case: (prop_inv (indom h1 (l, d2))).
  { move=> /[dup]/l1 fd ??. 
    rewrite fmapU_nin1 // fmapU_in1 // =><-.
    rewrite fmapNone //.
    case: (prop_inv (indom h2 (l, d1))).
    { move/l2/(fP _ _ _ fd); rewrite fE.
      case: (classicT (d2 = d1))=> [?|/[swap]/[apply] ]//.
      by subst. }
    by move/(@fmapNone _ _ _ _)->. }
  by move=> *; rewrite ?fmapNone.
Qed.

Implicit Type (H : hhprop Dom).

Lemma hsub_hstar_squash H1 H2 f fs1 fs2 : 
  hlocal H1 fs1 -> 
  hlocal H2 fs2 -> 
  (forall x y, x <> y -> indom fs1 x -> indom fs2 y -> f x <> f y) ->
    hsub (H1 \* H2) f = hsub H1 f \* hsub H2 f.
Proof.
  move=> l1 l2 fP; extens=> h; split.
  { case=> h'[<-][v][h1][h2][Hh1][Hh2][dj]?; subst.
    have?: valid_subst h1 (fun x : loc * Dom => (x.1, f x.2)).
    { applys* valid_subst_not_squash. }
    have?: valid_subst h2 (fun x : loc * Dom => (x.1, f x.2)).
    { by apply/valid_subst_union_l; eauto. }
    exists 
      (fsubst h1 (fun x => (x.1, f x.2))),
      (fsubst h2 (fun x => (x.1, f x.2))); splits.
    { exists h1; splits*. }
    { exists h2; splits*. }
    { apply/valid_subst_disj; eauto. }
    exact/fsubst_union_valid. }
  case=> ?[?][][h1][<-][v1]?[][h2][<-][v2]?[dj]->.
  have?: valid_subst (h1 \u h2) (fun x : loc * Dom => (x.1, f x.2)).
  { by apply/valid_subst_union; eauto. }
  exists (h1 \u h2); splits=> //.
  { exact/fsubst_union_valid. }
  exists h1 h2; splits=> //.
  apply/disjoint_of_not_indom_both=> -[l d] dm1 dm2.
  case: (disjoint_inv_not_indom_both dj (x := (l, f d))); 
  by rewrite fsubst_valid_indom; exists (l, d).
Qed.

Lemma hsub_hstar_fset_squash {A : Type} (Hi : A -> hhprop Dom) f fsi fs : 
  (forall i, indom fs i -> hlocal (Hi i) (fsi i)) -> 
  (forall x y i j, 
    indom fs i -> 
    indom fs j -> 
    i <> j -> 
    indom (fsi i) x -> 
    indom (fsi j) y -> f x <> f y) ->
    hsub (\*_(i <- fs) Hi i) f = \*_(i <- fs) hsub (Hi i) f.
Proof.
  elim/fset_ind: fs.
  { move=> *; rewrite? hbig_fset_empty (@hsub_idE Dom empty); autos*=> //. }
  move=> fs i IHfs ? hl fP.
  rewrite ?hbig_fset_update // (hsub_hstar_squash f (fs1 := fsi i) (fs2 := Union fs fsi)).
  { rewrite IHfs //.
    { move=> ??; apply/hl; rewrite indom_update_eq; by right. }
    move=> > ???; apply/fP=> //; rewrite indom_update_eq; by right. }
  { apply/hl; rewrite indom_update_eq; by left. }
  { apply/hlocal_hstar_fset=> ??? {}/hl hl ?? /hl ind.
    rewrite indom_Union; eexists; split; eauto. 
    apply/ind; rewrite indom_update_eq; by right. }
  move=> x y ? ind; rewrite indom_Union=> -[j][?]?.
  apply/(fP x y i j)=> //; rewrite ?indom_update_eq; try by (left+right).
  by move=> ?; subst.
Qed.


Lemma hsub_hstar_fset (fs fs' : fset Dom) (f : Dom -> Dom) R R' :
  (fsubst fs' f = fs) ->
  (forall d, indom fs' d -> hlocal (R' d) (single d tt)) ->
  (forall x, indom fs x -> hsub (\*_(d <- filter (fun y _ => f y = x) fs') R' d) f = R x) ->
  hsub (\*_(d <- fs') R' d) f = \*_(d <- fs) R d.
Proof.
  move=>  fsE lR ?.
  have fs'E: fs' = Union fs (fun d => filter (fun y _ => f y = d) fs').
  { apply/fset_extens=> x.
    rewrite indom_Union; split.
    { exists (f x); rewrite -fsE indom_fsubst filter_indom.
      by do ? eexists. }
    by case=> ? [_]; rewrite filter_indom=> -[]. }
  rewrite fs'E hbig_fset_Union; first last.
  { move=> *; apply/disjoint_of_not_indom_both=> ?.
    by rewrite ?filter_indom=> -[?]->[_] ?. }
  rewrite (hsub_hstar_fset_squash _ _ (fun i => filter (fun y : Dom => fun=> f y = i) fs')).
  { exact/hbig_fset_eq. }
  { move=> ??; apply/hlocal_hstar_fset=> ?.
    rewrite filter_indom=> -[]??; subst.
    move=> ? {}/lR lR ?? /lR /[! indom_single_eq]<- //.
    rewrite filter_indom; splits*; by exists. }
  by move=> > ???; rewrite ?filter_indom=> -[_]->[_]->.
Qed.


Lemma fsubst_union_valid' {A B C : Type}  `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) :
  disjoint fm1 fm2 ->
  valid_subst' fm1 f ->
  valid_subst' (fm1 \u fm2) f ->
    fsubst (fm1 \u fm2) f = 
    fsubst fm1 f \u fsubst fm2 f.
Proof.
  move=> dj v1 v2; apply/fmap_extens=> x.
  have v3: valid_subst' fm2 f.
  { move=> ?? ind1 ind2 /v2.
    rewrite ?fmapU_nin1=> [->||] //; rewrite ?indom_union_eq; eauto.
    all: apply/(disjoint_inv_not_indom_both);[|eauto]; autos*. }
  case: (prop_inv (indom (fsubst fm1 f) x))=> [/[dup]?|].
  { rewrite fmapU_in1 // fsubst_valid_indom=> -[]y[]<-?.
    have ind : (indom (fm1 \u fm2) y).
    { rewrite indom_union_eq; by left. }
    rewrite /fsubst {1 3}/fmap_data /map_fsubst.
    case: classicT=> [?|].
    { case: (indefinite_description _)=> ? []/v2/[apply]/(_ ind)->.
      case: classicT=> [?|].
      { case: (indefinite_description _)=> ? []/v1/[apply]-> //.
        by rewrite fmapU_in1. }
      case; by exists y. }
    case; by exists y. }
  move=> /[dup]?; rewrite fsubst_valid_indom.
  move=> ind; rewrite fmapU_nin1 //.
  rewrite /fsubst {1 3}/fmap_data /map_fsubst.
  case: classicT=> [?|].
  { case: (indefinite_description _)=> y [] fE ind1.
    have ind2: ~ indom fm1 y.
    { move=> ind2; apply/ind; by exists y. }
    have ?: indom fm2 y.
    { have: indom (fm1 \u fm2) y by [].
      rewrite indom_union_eq; by case. }
    rewrite fmapU_nin1 //; case: classicT=> [?|]; subst.
    { case: (indefinite_description _)=> ?[]??.
      apply/v3; eauto. }
    case; by exists y. }
    case: classicT=> // ?; case: (indefinite_description _)=> y []<-? [].
    exists y; split=> //.
    suff: indom (fm1 \u fm2) y by [].
    rewrite indom_union_eq; eauto.
Qed.

Lemma valid_subst_union_disjoint' {A B C : Type}  (fm1 fm2 : fmap A B) (f : A -> C) :
  disjoint fm1 fm2 ->
  valid_subst' (fm1 \u fm2) f ->
  valid_subst' fm1 f.
Proof.
  move=> dj v12 ?? ?? /v12.
  rewrite ?fmapU_in1 //; apply; rewrite* indom_union_eq.
Qed. 

Lemma valid_subst_union_disjoint'' {A B C : Type}  (fm1 fm2 : fmap A B) (f : A -> C) :
  disjoint fm1 fm2 ->
  valid_subst' (fm1 \u fm2) f ->
  valid_subst' fm2 f.
Proof.
  move=> dj v12 ?? ?? /v12.
  rewrite ?fmapU_nin1; first (apply; rewrite* indom_union_eq).
  all: apply/disjoint_inv_not_indom_both; [|eauto]; autos*.
Qed. 

Lemma fsubst_union_valid_disj' {A B C : Type}  `{Inhab B} (fm1 fm2 : fmap A B) (f : A -> C) :
  disjoint fm1 fm2 ->
  valid_subst' (fm1 \u fm2) f ->
    fsubst (fm1 \u fm2) f = 
    fsubst fm1 f \u fsubst fm2 f.
Proof.
  move=> dj v. 
  apply/fsubst_union_valid'=> //.
  exact/(valid_subst_union_disjoint' dj).
Qed.

Lemma fmapN0E A B (fm : fmap A B) : 
  (fm <> empty) = (exists y, indom fm y).
Proof.
  extens; split.
  { move=> neq. apply:not_not_inv; rewrite not_exists_eq=> ind.
    apply/neq/fmap_extens=> /=?.
    apply:not_not_inv; exact/ind. }
  by case=> ? /[swap]->.
Qed.

Lemma fsubst_Union_valid_fset' {A C T : Type} fmj (fmi : T -> fset A)  (f : A -> C) fs :
  valid_subst (Union fs fmi) f ->
  (forall i j : T, i <> j -> disjoint (fmi i) (fmi j)) ->
  (forall i, indom fs i -> fsubst (fmi i) f = fmj i) ->
    fsubst (Union fs fmi) f = Union fs fmj.
Proof.
  move=> v.
  have{v}: valid_subst' (Union fs fmi) f by move=>*; exact/v.
  move=> + dj; elim/fset_ind: fs=> //.
  { by rewrite ?Union0 fsubst_empty. }
  move=> fs x IHfs ? /[! @Union_upd_fset] // fsb fmiE.
  have?: disjoint (fmi x) (Union fs fmi).
  { by rewrite disjoint_Union=> z ?; apply/dj=> ?; subst. }
  rewrite fsubst_union_valid_disj' //.
  rewrite IHfs // ?fmiE // ?indom_update_eq; first by left.
  { by apply/valid_subst_union_disjoint''; [|eauto]. }
  move=> *; apply/fmiE; rewrite* indom_update_eq.
Qed.

Lemma fsubst_Union_valid' {A B C T : Type} fm y `{Inhab B} (fmi : T -> fmap A B)  (f : A -> C) fs :
  valid_subst (Union fs fmi) f ->
  (forall i j : T, i <> j -> disjoint (fmi i) (fmi j)) ->
  (forall i, indom fs i -> fsubst (fmi i) f = fm) ->
  indom fs y ->
    fsubst (Union fs fmi) f = fm.
Proof.
  move=> v.
  have{v}: valid_subst' (Union fs fmi) f by move=>*; exact/v.
  move=> + dj; elim/fset_ind: fs y=> // fs x IHfs ? y /[! @Union_upd] // fsb fmiE; autos*.
  case: (prop_inv (fs = empty))=> [?|/[! fmapN0E]-[y' ?] ]; subst.
  { rewrite Union0 union_empty_r=> /[dup]/fmiE /[swap].
    by rewrite indom_update_eq=> -[->|]. }
  have?: disjoint (fmi x) (Union fs fmi).
  { by rewrite disjoint_Union=> z ?; apply/dj=> ?; subst. }
  rewrite fsubst_union_valid_disj' //.
  rewrite (IHfs y') // ?fmiE ?union_self // ?indom_update_eq; first by left.
  { by apply/valid_subst_union_disjoint''; [|eauto]. }
  move=> *; apply/fmiE; rewrite* indom_update_eq.
Qed.

Arguments fsubst_Union_valid' {_ _ _ _} _ _.

(* map family localization *)
Definition fm_localize {A B C} (fs : fset A) (fmi : A -> fmap C B) := ((fmi \u_ fs) (fun=> empty)).

Lemma Union_localization {A B C} (fs : fset A) (fmi : A -> fmap C B) : 
  (forall i j, indom fs i -> indom fs j -> i <> j -> disjoint (fmi i) (fmi j)) ->
  Union fs fmi = Union fs (fm_localize fs fmi).
Proof.
  intros. unfold Union, fm_localize. apply fold_fset_eq.
  intros. extens. intros. unfold uni. case_if; eqsolve.
Qed.

Fact fm_localization {A B C} (fs : fset A) (fmi : A -> fmap C B) : 
  (forall i j, indom fs i -> indom fs j -> i <> j -> disjoint (fmi i) (fmi j)) ->
  forall i j, i <> j -> disjoint (fm_localize fs fmi i) (fm_localize fs fmi j).
Proof.
  intros. apply disjoint_of_not_indom_both.
  intros. unfold fm_localize, uni in H1, H2. repeat case_if.
  2-4: simpl in H1, H2; unfolds indom, map_indom; eqsolve.
  revert H1 H2. apply disjoint_inv_not_indom_both, H; auto.
Qed.

Lemma Union_eq {A B C} (fs : fset A) (fmi1 fmi2 : A -> fmap C B) : 
  (forall i j, i <> j -> disjoint (fmi1 i) (fmi1 j)) ->
  (forall i j, i <> j -> disjoint (fmi2 i) (fmi2 j)) ->
  (forall x, indom fs x -> fmi1 x = fmi2 x) -> 
  Union fs fmi1 = Union fs fmi2.
Proof.
  move=> ??.
  elim/fset_ind: fs.
  { by rewrite ?Union0. }
  move=> fs x IHfs ? fmiE. rewrite ?Union_upd //; autos*; rewrite IHfs.
  { fequal; apply/fmiE; rewrite* indom_update_eq. }
  move=> *; apply/fmiE; rewrite* indom_update_eq.
Qed.

Lemma Union_eq_fset {A B} (fs : fset A) (fsi1 fsi2 : A -> fset B) : 
  (forall x, indom fs x -> fsi1 x = fsi2 x) -> 
  Union fs fsi1 = Union fs fsi2.
Proof.
  elim/fset_ind: fs.
  { by rewrite ?Union0. }
  move=> fs x IHfs ? fsiE. rewrite ?Union_upd_fset //; autos*; rewrite IHfs.
  { fequal; apply/fsiE; rewrite* indom_update_eq. }
  move=> *; apply/fsiE; rewrite* indom_update_eq.
Qed.

Fact interval_point_segmentation i j :
  Union (interval i j) (fun i => single i tt) = interval i j.
Proof.
  apply fset_extens. intros x. 
  rewrite indom_Union indom_interval.
  setoid_rewrite indom_interval. setoid_rewrite indom_single_eq.
  split. by intros (? & ? & <-). eauto.
Qed.

Lemma hstar_fsetE {A} (fs : fset A) (H : A -> hhprop Dom) h :
  (\*_(d <- fs) H d) h = 
  exists hi, 
    h = Union fs hi /\ 
    (forall i j, i <> j -> disjoint (hi i) (hi j)) /\
    (forall i, indom fs i -> H i (hi i)).
Proof.
  elim/fset_ind: fs=> [|fs x IHfs ?] in h *.
  { extens; rewrite hbig_fset_empty; split.
    { move=> /hempty_inv->; exists (fun _ : A => empty : hheap Dom); splits=> //.
      by rewrite Union0. }
    by case=> ? []/[! @Union0]->. }
  rewrite hbig_fset_update //; extens; split.
  { case=> h1 [h2][?][]/[! IHfs]-[hi][]->[]dj ind[].
    rewrite disjoint_Union=> dj' ->.
    have?: forall j, disjoint h1 ((hi \u_ fs) (fun=> empty) j).
    { move=> ?. rewrite /uni; case: classicT=> // /dj'; autos*. }
    have?: forall i j, i <> j -> disjoint ((hi \u_ fs) (fun=> empty) i) ((hi \u_ fs) (fun=> empty) j).
    { move=> *; rewrite /uni; do ? case: classicT=> //; autos*. }
    exists (upd (hi \u_fs (fun=> empty)) x h1); splits.
    { rewrite Union_upd ?upd_eq; autos*.
      { fequal; apply/Union_eq=> // ??.
        {  move=> *; rewrite /upd; do ? case: classicT=> ?; subst; autos*. } 
        rewrite upd_neq // ?uni_in // => ?; by subst. }
      move=> ? j ?; rewrite /upd; do ? (case: classicT=> ?; subst=> //); autos*. }
    { move=> *; rewrite /upd; do ? case: classicT=> ?; subst; autos*. }
    move=> ?; rewrite indom_update_eq=> -[<-|/[dup]?/ind?].
    { by rewrite upd_eq. }
    rewrite upd_neq ?uni_in // => ?; by subst. }
  case=> hi[->][dj] ind; rewrite Union_upd //; autos*.
  exists (hi x), (Union fs hi); splits=> //.
  { apply/ind; rewrite* indom_update_eq. }
  { rewrite IHfs; exists hi; splits=> // ??.
    apply/ind; rewrite* indom_update_eq. }
  by rewrite disjoint_Union=> *; apply/dj=> ?; subst.
Qed.

Local Notation D := Dom. 
Local Notation hhprop := (hhprop Dom). 

Fact hsinglestar_fset_inv {A : Type} (fs : fset A) : forall (d : D) (p : A -> loc) (v : A -> val) h,
  (\*_(a <- fs) ((p a) ~(d)~> (v a))) h -> 
  h = Union fs (fun a => single ((p a), d) (v a)) /\
  forall a1 a2, indom fs a1 -> indom fs a2 -> a1 <> a2 -> p a1 <> p a2.
Proof.
  intros.
  pose proof H as H'. rewrite hstar_fsetE in H'.
  destruct H' as (hi & Eh & Hdj & HH).
  assert (forall i, indom fs i -> hi i = single (p i, d) (v i)) as HH'.
  { intros. apply HH, hsingle_inv in H0. by rewrite H0. }
  assert (forall a1 a2 : A,
    indom fs a1 -> indom fs a2 -> a1 <> a2 -> p a1 <> p a2) as Hr.
  { intros. apply HH' in H0, H1. pose proof (Hdj _ _ H2) as Htmp.
    rewrite -> H0, H1 in Htmp. intros E'. rewrite E' in Htmp.
    by apply disjoint_single_single_same_inv in Htmp.
  }
  split; try assumption.
  subst h.
  etransitivity. 2: symmetry; apply Union_localization.
  2:{ 
    intros. apply disjoint_single_single. intros ?.
    inversion H3. revert H5. by apply Hr.
  }
  apply Union_eq; try assumption.
  {
    apply fm_localization.
    intros. apply disjoint_single_single. intros ?.
    inversion H3. revert H5. by apply Hr.
  }
  { intros. unfold fm_localize, uni. rewrite HH'; auto. case_if; eqsolve. }
Qed.

Lemma aux {T} fsi i (fmi : T -> hheap D) fs x l :
  (forall z, indom fs z -> local (fsi z) (fmi z)) ->
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  (forall i j, i <> j -> disjoint (fmi i) (fmi j)) ->
  indom fs i -> indom (fsi i) x ->
  fmap_data (Union fs fmi) (l, x) = fmap_data (fmi i) (l, x).
Proof.
  move=> + dj1 dj2.
  elim/fset_ind: fs i=> // fs y IHfs ? t lc.
  have lc': forall z : T, indom fs z -> local (fsi z) (fmi z).
  { move=> *; apply/lc; rewrite* indom_update_eq. }
  rewrite indom_update_eq=> -[<-|].
  { rewrite Union_upd // =>?; autos*; rewrite fmapU_nin2 //.
    rewrite indom_Union=> -[]?[]/[dup]?/lc'/[apply].
    apply/disjoint_inv_not_indom_both; last eauto.
    apply/dj1=> ?; by subst. }
  move=> ind1 ind2.
  have ? : ~ indom (fmi y) (l, x).
  { move/lc=> ind. apply/(disjoint_inv_not_indom_both (dj1 t y _)); eauto.
    { move=> ?; by subst. }
    exact/ind/indom_update. }
  rewrite Union_upd //; autos*; rewrite fmapU_nin1 ?(IHfs t) //.
Qed.

Lemma local_single_fsubst (f : D -> D) h x: 
  local (single x tt) h -> 
  local (single (f x) tt) (fsubst h (fun x => (x.1, f x.2))).
Proof.
  move=> lc >; rewrite fsubst_valid_indom=> -[][??][][->]<-/lc.
  by rewrite ?indom_single_eq=>->.
Qed.

Lemma hlocal_single_hsub (f : D -> D) x H:  
  hlocal H (single x tt) -> 
  hlocal (hsub H f) (single (f x) tt).
Proof. by move=> lc ?[h'][]<-[_]/lc/(local_single_fsubst f). Qed.

Lemma hsub_squash f fs R x y R':
  (f y = x) ->
  indom fs y ->
  (forall x x', x <> x' -> f x = f x' -> indom fs x /\ indom fs x') ->
  (forall d, hlocal (R d) (single d tt)) ->
  (forall d, indom fs d -> f d = x -> hlocal (R' d) (single d tt)) ->
  (forall h d, 
    indom fs d -> 
    f d = x -> 
    local (single d tt) h ->
      R' d h <-> R x (fsubst h (fun z => (z.1, f z.2)))) ->
  hsub (\*_(d <- filter (fun y : D => fun=> f y = x) fs) R' d) f =
  R x.
Proof.
  move=> <- ? fP lR' lR RP.
  extens=> h; split.
  { case=> h' [<-][]/[swap].
    rewrite hstar_fsetE=> -[hi][->][].
    do ? setoid_rewrite filter_indom=> //.
    move=> ? R'h v.
    have R'hiy: R' y (hi y) by apply/R'h.
    have lhiy: local (single y tt) (hi y) by apply/lR.
    rewrite (fsubst_Union_valid' (fsubst (hi y) (fun x0 : loc * D => (x0.1, f x0.2))) y) //;
    try setoid_rewrite filter_indom=> //.
    { apply/RP; eauto. }
    move=> z[]? fE.
    have R'hiz: R' z (hi z) by apply/R'h.
    have lhiz: local (single z tt) (hi z) by apply/lR.
    apply/fmap_extens=> -[l w].
    case: (prop_inv (w = f y))=> [->|].
    { rewrite -{1}fE.
      have hiE: forall l, fmap_data (hi z) (l, z) = fmap_data (hi y) (l, y).
      { move=> {}l. 
        move: (v (l, z) (l, y))=> /= /[! fE]/(_ eq_refl).
        rewrite 
          (@aux _ (fun x => single x tt) z) 
          ?(@aux _ (fun x => single x tt) y) //;
        try setoid_rewrite filter_indom=> //.
        2,4: by move=>*; apply disjoint_single_single.
        all: move=> ?[]??; apply/ lR=> //; exact/R'h. }
      case: (prop_inv (indom (hi z) (l, z)))=> [ind/=|].
      { rewrite /map_fsubst; case: classicT.
        { move=> pf; case: (indefinite_description _)=> -[]/=?? [][]->_/lhiz.
          rewrite indom_single_eq=><-.
          case: classicT=> [?|].
          { case: (indefinite_description _)=> -[]/=?? [][]->_/lhiy.
            by rewrite indom_single_eq=><-. }
          case; exists (l, y); split=> //.
          by rewrite /map_indom -hiE. }
        case; by exists (l, z). }
      move=> ?; rewrite ?fmapNone // fsubst_valid_indom.
      all: move=> -[][??][]/=[]-> _ /[dup].
      { move/lhiy; rewrite indom_single_eq=> <-.
        by rewrite /indom /map_indom -hiE. }
      by move/lhiz; rewrite indom_single_eq=> <-. }
    move=> ?. rewrite ?fmapNone // fsubst_valid_indom=> -[][??][]/=[]_/[swap].
    { by move/lhiy; rewrite indom_single_eq=> <-?; subst. }
    by move/lhiz; rewrite indom_single_eq=> <-?; subst. }
  move=> /[dup] /lR' lh Rh.
  set (h' := 
    Union (filter (fun x _=> f x = f y) fs) (fun d => fsubst h (fun x => (x.1, d)))).
  have ?: forall z,
    indom (filter (fun x0 : D => fun=> f x0 = f y) fs) z ->
    local (single z tt) (fsubst h (fun x0 : loc * D => (x0.1, z))).
  { move=> >; rewrite filter_indom=> _; exact/local_single_fsubst/lh. }
  have?: forall i j : D, i <> j -> disjoint (single i tt) (single j tt).
  { move=> ??; exact/disjoint_single_single. }
  have ?: valid_subst h' (fun x0 => (x0.1, f x0.2)).
  { case=> ? d1[l d2]/=[->]/[dup]fE.
    case: (prop_inv (d1 = d2))=> [->|] // /fP/[apply]-[ind1 ind2].
    case: (prop_inv (f y = f d1))=> [ffE|].
    { have?: forall i j : D,
      i <> j -> disjoint (fsubst h (fun x => (x.1, i))) (fsubst h (fun x => (x.1, j))).
      { move=> *; apply/disjoint_of_not_indom_both=> -[??].
        by rewrite ?fsubst_valid_indom=> /[swap]-[][]/=??[][]_<-_[] ?[][]. }
      rewrite /h' 
      (@aux _ (fun x => single x tt) d1)
      ?(@aux _ (fun x => single x tt) d2)
      ?filter_indom -?fE // -?ffE //=.
      rewrite /map_fsubst. case: classicT=> [pf|].
      { case: (indefinite_description _)=> -[??][]/=[->]/lh.
        rewrite indom_single_eq=><-.
        case: classicT=> [?|].
        { case: (indefinite_description _)=> -[??][]/=[->]/lh.
          by rewrite indom_single_eq=><-. }
        case: pf=> -[]? d'/=[][->]? []; by exists (l, d'). }
      case: classicT=> // /[dup]-[][]? d' /=[][->]??[].
      by exists (l, d'). }
    move=> N; rewrite /h'.
    rewrite ?fmapNone // indom_Union=> -[]?[] /[! @filter_indom]/[! @fsubst_valid_indom].
    all: by case=> ? ffE[][??]/=[][->]?; subst; rewrite -ffE fE in N. }
  have ?: forall i j : D,
    i <> j ->
    disjoint (fsubst h (fun x=> (x.1, i))) (fsubst h (fun x => (x.1, j))).
  { move=> > ?; apply/disjoint_of_not_indom_both=> -[??].
    move/local_single_fsubst=> /(_ _ lh).
    rewrite indom_single_eq=>?; subst.
    move/local_single_fsubst=> /(_ _ lh).
    by rewrite indom_single_eq=>?; subst. }
  have ffE: forall i, f i = f y ->
    fsubst (fsubst h (fun x => (x.1, i))) (fun x => (x.1, f x.2)) = h.
  { move=> ? fE.
    by apply/fsubst_cancel'=> -[??]/= /lh; rewrite indom_single_eq fE=> ->. }
  exists h'; splits=> //.
  { rewrite (fsubst_Union_valid' h y) //; 
    try setoid_rewrite filter_indom=> //.
    by move=> ?[?]?; rewrite ffE. }
  rewrite hstar_fsetE.
  exists (fun d => fsubst h (fun x : loc * D => (x.1, d : D))); splits=> //.
  move=> ?; rewrite filter_indom=> -[]? fE.
  apply/RP=> //; [apply/local_single_fsubst;eauto|].
  by rewrite ffE.
Qed.

Lemma eq_fsubst {A C} (fm : fset A) (f g : A -> C) :
  (forall x, indom fm x -> f x = g x) ->
  fsubst fm f = fsubst fm g.
Proof.
  move=> fE; apply/fmap_extens=> ? /=.
  rewrite /map_fsubst; case: classicT=> [pf|].
  { case: (indefinite_description _)=> ?[]?.
    case: classicT=> [?|].
    { case: (indefinite_description _)=> ?[?].
      by rewrite /map_indom; do ? case: (fmap_data _ _)=> // -[]. }
    case: pf=> y[fE' ?][]; rewrite -fE' fE //; by exists y. }
  case: classicT=> // /[dup]-[y][fE' ?]_[]; rewrite -fE' -fE //; by exists y.
Qed.



Lemma hsub_hstar_can g f H Q : 
  cancel f g ->
  hsub (H \* Q) f = hsub H f \* hsub Q f.
Proof.
  move=> c1; extens.
  have?: forall h : hheap D, valid_subst h (fun x => (x.1, f x.2)).
  { move=> ?; exact/(valid_subst_can c1). }
  split.
  { case=> h'[]<-[]?[h1][h2][?][?][?]->.
    exists 
      (fsubst h1 (fun x : loc * D => (x.1, f x.2))),
      (fsubst h2 (fun x : loc * D => (x.1, f x.2))); splits=> //.
    1-2: exists; splits*.
    { exact/valid_subst_disj. }
    exact/fsubst_union_valid. }
  case=> ?[?][][h1][<-][?]?[][h2][<-][?]?[]?->.
  exists (h1 \u h2); splits.
  { exact/fsubst_union_valid. }
  { exact/valid_subst_union. }
  exists h1, h2; splits=> //; exact/valid_subst_disj_inv.
Qed.

Lemma hsub_hempty f : 
  hsub \[] f = \[] :> hhprop.
Proof.
  extens=> h; split=> [|/hempty_inv->].
  { case=> h'[]<-[]?/hempty_inv->; by rewrite fsubst_empty. }
  by exists (empty : hheap D); rewrite fsubst_empty.
Qed.


Lemma hsub_hstar_fstar_can {A} g f (H : A -> _) (fs : fset A) : 
  cancel f g ->
  hsub (\*_(i <- fs) H i) f = \*_(i <- fs) hsub (H i) f :> hhprop.
Proof.
  move=> c; elim/fset_ind: fs=> [|fs x IHfs ?].
  { by rewrite ?hbig_fset_empty hsub_hempty. }
  by rewrite ?hbig_fset_update // (hsub_hstar_can _ _ c) IHfs.
Qed.

Lemma hstar_fset_eq_restr {A B} (R : B -> hhprop) fs (f : A -> B) : 
  injective_restr fs f ->
  \*_(d <- fs) R (f d) = \*_(d <- fsubst fs f) R d.
Proof.
  elim/fset_ind: fs=> [|fs x IHfs Hnotin] Hinj.
  { by rewrite fsubst_empty ?hbig_fset_empty. }
  replace (fsubst _ _) with (update (fsubst fs f) (f x) tt) 
    by now rewrite fsubst_update_valid_restr.
  pose proof Hinj as Hinj'%inj_restr_update.
  rewrite ?hbig_fset_update // ?IHfs // indom_fsubst=> HH.
  destruct HH as (y & E & Hin). apply Hnotin.
  apply Hinj in E; try (rewrite indom_update_eq; tauto). congruence.
Qed.

Lemma hstar_fset_eq {A B} (R : B -> hhprop) fs (f : A -> B) g : 
  cancel f g ->
  \*_(d <- fs) R (f d) = \*_(d <- fsubst fs f) R d.
Proof.
  move=> c.
  elim/fset_ind: fs=> [|fs x IHfs ?].
  { by rewrite fsubst_empty ?hbig_fset_empty. }
  rewrite (fsubst_update _ _ _ c) ?hbig_fset_update // ?IHfs //.
  by rewrite indom_fsubst=> -[?][]/(can_inj c)->.
Qed.

Lemma hsub_hstar {A} (H : A -> hhprop) (f : D -> D) : 
  hsub (\exists a, H a) f =
  \exists a, hsub (H a) f.
Proof.
  extens=> ?; split.
  { case=> h'[]<- []? []a ?.
    exists a, h'; splits*. }
  case=> a []h'[]<-[]??.
  exists h'; splits*; by exists a.
Qed.



Section WP_for.

Context (fs fs' : fset D).
Context (ht : D -> trm).
Context (Inv : int -> hhprop).
Context (R R' : D -> hhprop).
Context (m : val -> val -> val) (vd : val -> Prop).
Context (H : int -> hhprop).
Context (H' : int -> (D -> val) -> hhprop).
Context (Z N : int).
Context (C : trm).
Context (fsi : int -> fset D).
Context (P : hhprop).
Context (Q : (D -> val) -> hhprop).
Context (vr : var).
Context (fsi' : int -> fset D).
Context (fi  : int -> D -> D).
Context (gi  : int -> D -> D).
Context (f g : D -> D).
Context (ht' : D -> trm).


Hypotheses (CM : comm m) (AS : assoc m) (VM : forall x y, (vd x /\ vd y) <-> vd (m x y)).
Hypotheses Pimpl : 
  (P ==>  
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi) R d) \*
    \(m, vd)_(i <- interval Z N) H i).
Hypothesis ZLN : Z <= N.
Hypotheses fsE : fs = Union (interval Z N) fsi.
Hypotheses fsDfs' : disjoint fs' fs.
Hypotheses htE : forall x, indom fs' x -> ht x = For Z N (trm_fun vr C).

Hypotheses lI  : forall i, hlocal (Inv i) fs'.
Hypotheses lH  : forall i, hlocal (H i) fs'.
Hypotheses lH' : forall i v, hlocal (H' i v) fs'.
Hypotheses lR  : forall i, hlocal (R i) (single i tt).
Hypotheses lR' : forall i, hlocal (R' i) (single i tt).

Definition Fs := Union (interval Z N) fsi'.

Hypotheses C1       : forall i, cancel (fi i) (gi i).
Hypotheses C2       : forall i, cancel (gi i) (fi i).
Hypotheses fiIm     : forall i, fsubst (fsi' i) (fi i) = fsi i.
Hypotheses fRestr   : forall i x, indom (interval Z N) i -> indom (fsi' i) x -> f x = fi i x.
Hypotheses fGlue    : forall x x', x <> x' -> f x = f x' -> indom Fs x /\ indom Fs x'.
Hypotheses fIm      : forall x, indom (fsubst (fs' \u Fs) f) x <-> indom (fs' \u Fs) (g x).
Hypotheses fC       : forall i, indom (fs' \u fs) i -> f (g i) = i.
Hypotheses fid      : forall i, indom fs' i -> f i = i.
Hypotheses giid      : forall i j, indom fs' i -> gi j i = i.
Hypotheses ht'E     : ht' \o f = ht.
Hypotheses fs'Dfsi' : forall i, indom (interval Z N) i -> disjoint (fsi' i) fs'.
Hypotheses fsDfsi' : forall i, indom (interval Z N) i -> disjoint (fsi i) fs'.
Hypotheses fsi'D : forall i j, i <> j -> disjoint (fsi' i) (fsi' j).

Hypotheses Qimpl : 
  forall hv,
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi) R' d) \* 
    (\(m, vd)_(i <- interval Z N) H' i (hv \o f)) ==> Q hv.

Hypotheses HE :   
  forall (hv hv' : D -> val) m, 
    Z <= m < N ->
    (forall i, indom (fsi' m) i -> hv(i) = hv'(i)) ->
      H' m hv = H' m hv'.
Hypothesis IH : (forall l Q, Z <= l < N -> 
    Inv l \* 
    (\*_(d <- fsi l) R d) \* 
    Q \(m, vd) H l ==> 
      wp (fs' \u fsi l) 
        ((fun=> subst vr l C) \u_fs' ht) 
        (fun hr => 
            Inv (l + 1) \* 
            (\*_(d <- fsi l) R' d) \* 
            Q \(m, vd) H' l (hr \o f))).


Definition Gi (x : D) :=
  match classicT (exists i, indom (interval Z N) i /\ indom (fsi' i) x) with 
  | left P => 
    let '(@exist _ _ a _) := indefinite_description P in gi a
  | _ => id
  end.

Lemma Gi_in i x : 
  indom (interval Z N) i ->
  indom (fsi' i) x ->
    Gi x = gi i.
Proof.
  move=> ??; rewrite /Gi; case: classicT=> [?|[] ].
  { case: (indefinite_description _)=> j [] ? /=.
    case: (prop_inv (i = j))=> [->|]// /fsi'D.
    move/(@disjoint_inv_not_indom_both _ _ _ _ _)/[apply].
    by case. }
  by exists i.
Qed.

Arguments Gi_in : clear implicits.
  

Lemma hsub_P :
  hsub (
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi') hsub (R (f d)) (Gi d)) \*
    \(m, vd)_(i <- interval Z N) H i) f = 
    Inv Z \* 
    (\*_(d <- Union (interval Z N) fsi) R d) \*
    \(m, vd)_(i <- interval Z N) H i.
Proof.
  rewrite (@hsub_hstar_id_l _ fs') //; first last.
  { move=> > /fGlue/[apply]-[??]. 
    split; apply/disjoint_inv_not_indom_both; [|eauto| |eauto];
    by rewrite /= /Fs disjoint_Union. }
  rewrite (@hsub_hstar_id_r _ fs') //; first last.
  { exact/hlocal_hmerge_fset. }
  { move=> > /fGlue/[apply]-[??]. 
    split; apply/disjoint_inv_not_indom_both; [|eauto| |eauto];
    by rewrite /= /Fs disjoint_Union. }
  do ? fequals. 
  erewrite hsub_hstar_fset; first reflexivity.
  { rewrite (fsubst_Union_valid_fset' fsi) //.
    { move=> x1 x2; case:(prop_inv (x1 = x2))=>[->|]//.
      move/fGlue/[apply]=>-[]; rewrite /Fs/ indom/map_indom.
      by do ? case: (fmap_data _ _)=> // -[]. }
      move=> ??; rewrite -fiIm; apply/eq_fsubst=> ? /fRestr.
      exact. }
  { move=> d; rewrite indom_Union=> -[i][??]?.
    case=> ?[<-][?]/lR /(local_single_fsubst (Gi d)).
    rewrite (Gi_in i) // (@fRestr i) // ?C1 //. }
  move=> x ind.
  set (B := hbig_fset _ _ _).
  have->: B = 
    \*_(d <- filter (fun y _ => f y = x) 
      (Union (interval Z N) fsi')) hsub (R x) (Gi d).
  { by apply/hbig_fset_eq=> ?; rewrite filter_indom=> -[_]->. }
  have[y]: exists y, indom Fs y /\ f y = x.
  { move: ind; rewrite indom_Union=> -[i][?].
    rewrite -fiIm indom_fsubst=>-[z][<-]?; exists z; split.
    { rewrite /Fs indom_Union; by exists i. }
    exact/fRestr. }
  case=> ? <-.
  apply/hsub_squash=> //.
  { move=> d; rewrite indom_Union=> -[i][]??<-.
    rewrite (Gi_in i) // -{2}[d] (C1 i) (@fRestr i) //.
    exact/hlocal_single_hsub. }
  move=> h d; rewrite indom_Union=> -[i][]??<- lh.
  rewrite (Gi_in i) //; split.
  { case=> h' []<-[?] Rh.
    rewrite fsubst_cancel' // => -[]??/= /(lR Rh).
    rewrite indom_single_eq=> <-.
    by rewrite {1}[f d] (@fRestr i) // C1. }
  move=> Rh; eexists; splits*.
  { rewrite fsubst_cancel' // => -[]??/= /lh.
    rewrite indom_single_eq=> <-.
    by rewrite {1}[f d] (@fRestr i) // C1. }
  by case=> ??[??] /=[->]/(congr1 (fi i))/[! C2]->.
Qed.

Lemma fsubst_fs :  fsubst Fs f = fs.
Proof.
  rewrite /Fs fsE (fsubst_Union_valid_fset' fsi) //.
  { move=> x1 x2; case:(prop_inv (x1 = x2))=>[->|]//.
    move/fGlue/[apply]=>-[]; rewrite /Fs/ indom/map_indom.
    by do ? case: (fmap_data _ _)=> // -[]. }
  move=> ??; rewrite -fiIm; apply/eq_fsubst=> ? /fRestr.
  exact.
Qed.

Lemma fsubst_fsi i :  fsubst (fsi i) (gi i) = fsi' i.
Proof. by rewrite -fiIm fsubst_cancel' // => ?? /[! C1]. Qed.


Lemma fsubst_fs' : fsubst fs' f = fs'.
Proof.
  rewrite (eq_fsubst _ id) //; apply/fmap_extens=> x.
  by rewrite fsubst_valid_eq // => ??->.
Qed.

Lemma fsubst_fs'_gi l : fsubst fs' (gi l) = fs'.
Proof.
  rewrite (eq_fsubst _ id)=> [|?/giid] //; apply/fmap_extens=> x.
  by rewrite fsubst_valid_eq // => ??->.
Qed.

Lemma fsubst_fs'_fi l : fsubst fs' (fi l) = fs'.
Proof.
  rewrite (eq_fsubst _ id)=> [|?/(giid l) {1}<- /[! C2] ] //; apply/fmap_extens=> x.
  by rewrite fsubst_valid_eq // => ??->.
Qed.

Lemma fsubst_fs'Ufs : fsubst (fs' \u Fs) f = fs' \u fs.
Proof.
  rewrite fsubst_union_valid_disj' ?fsubst_fs' ?fsubst_fs // /Fs ?disjoint_Union //.
  move=> >; rewrite /indom /map_indom.
  by do 2? case: (fmap_data _ _)=> // -[].
Qed.

Lemma fsubst_fs'Ufsi i : indom (interval Z N) i -> fsubst (fs' \u fsi i) (gi i) = fs' \u fsi' i.
Proof.
  move=> ?.
  rewrite fsubst_union_valid_disj' ?fsubst_fs'_gi ?fsubst_fsi // 1?disjoint_comm.
  { exact/fsDfsi'. }
  by move=> > ?? /(can_inj (C2 _))->.
Qed.


Lemma hsub_Q :
  (fun v => hsub (
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi') hsub (R' (f d)) (Gi d)) \*
    \(m, vd)_(i <- interval Z N) H' i (v \o f)) f) = fun v =>
    Inv N \* 
    (\*_(d <- Union (interval Z N) fsi) R' d) \*
    \(m, vd)_(i <- interval Z N) H' i (v \o f).
Proof.
  apply/fun_ext_1=> ?.
  rewrite (@hsub_hstar_id_l _ fs') //; first last.
  { move=> > /fGlue/[apply]-[??]. 
    split; apply/disjoint_inv_not_indom_both; [|eauto| |eauto];
    by rewrite /= /Fs disjoint_Union. }
  rewrite (@hsub_hstar_id_r _ fs') //; first last.
  { exact/hlocal_hmerge_fset. }
  { move=> > /fGlue/[apply]-[??]. 
    split; apply/disjoint_inv_not_indom_both; [|eauto| |eauto];
    by rewrite /= /Fs disjoint_Union. }
  do ? fequals.
  erewrite hsub_hstar_fset; first reflexivity.
  { by rewrite -fsE -fsubst_fs. }
  { move=> d; rewrite indom_Union=> -[i][??]?.
    case=> ?[<-][?]/lR' /(local_single_fsubst (Gi d)).
    by rewrite (Gi_in i) // (@fRestr i) // C1. }
  move=> x ind.
  set (B := hbig_fset _ _ _).
  have->: B = 
    \*_(d <- filter (fun y _ => f y = x) 
      (Union (interval Z N) fsi')) hsub (R' x) (Gi d).
  { by apply/hbig_fset_eq=> ?; rewrite filter_indom=> -[_]->. }
  have[y]: exists y, indom Fs y /\ f y = x.
  { move: ind; rewrite indom_Union=> -[i][?].
    rewrite -fiIm indom_fsubst=>-[z][<-]?; exists z; split.
    { rewrite /Fs indom_Union; by exists i. }
    exact/fRestr. }
  case=> ? <-.
  apply/hsub_squash=> //.
  { move=> d; rewrite indom_Union=> -[i][]??<-.
    rewrite (Gi_in i) // -{2}[d] (C1 i) (@fRestr i) //.
    exact/hlocal_single_hsub. }
  move=> h d; rewrite indom_Union=> -[i][]??<- lh.
  rewrite (Gi_in i) //; split.
  { case=> h' []<-[?] Rh.
    rewrite fsubst_cancel' // => -[]??/= /(lR' Rh).
    rewrite indom_single_eq=> <-.
    by rewrite {1}[f d] (@fRestr i) // C1. }
  move=> Rh; eexists; splits*.
  { rewrite fsubst_cancel' // => -[]??/= /lh.
    rewrite indom_single_eq=> <-.
    by rewrite {1}[f d] (@fRestr i) // C1. }
  by case=> ??[??] /=[->]/(congr1 (fi i))/[! C2]->.
Qed.

Lemma hsub_Pi l Q' : 
  hlocal Q' fs' ->
  Z <= l < N ->
  hsub (
    Inv l \* 
    (\*_(d <- fsi' l) R (f d)) \* 
    Q' \(m, vd) H l) (gi l) = 
  Inv l \* 
  (\*_(d <- fsi' l) hsub (R (f d)) (gi l)) \* 
  Q' \(m, vd) H l.
Proof.
  move=> ??.
  rewrite (@hsub_hstar_id_l _ fs') //; first last.
  { by move=> > /[swap] /(can_inj (C2 l))->. }
  { by move=> ? /giid. }
  rewrite (@hsub_hstar_id_r _ fs') //; first last.
  { exact/hlocal_hmerge. }
  { by move=> > /[swap] /(can_inj (C2 l))->. }
  { by move=> ? /giid. }
  by rewrite (hsub_hstar_fstar_can _ _ (C2 _)).
Qed.

Lemma hsub_Qi l Q' : 
  hlocal Q' fs' ->
  Z <= l < N ->
  (fun v => hsub (
    Inv (l + 1) \* 
    (\*_(d <- fsi' l) R' (f d)) \* 
    Q' \(m, vd) H' l v) (gi l)) = 
  fun v => Inv (l + 1) \* 
  (\*_(d <- fsi' l) hsub (R' (f d)) (gi l)) \* 
  Q' \(m, vd) H' l v.
Proof.
  move=> ??; apply/fun_ext_1=> ?.
  rewrite (@hsub_hstar_id_l _ fs') //; first last.
  { by move=> > /[swap] /(can_inj (C2 l))->. }
  { by move=> ? /giid. }
  rewrite (@hsub_hstar_id_r _ fs') //; first last.
  { exact/hlocal_hmerge. }
  { by move=> > /[swap] /(can_inj (C2 l))->. }
  { by move=> ? /giid. }
  by rewrite (hsub_hstar_fstar_can _ _ (C2 _)).
Qed.

Lemma wp_for_hbig_op_na_bis :
  (forall t, subst "for" t C = C) ->
  (forall t, subst "cnt" t C = C) ->
  (forall t, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
    P ==> wp (fs' \u fs) ht Q.
Proof.
  move=> *.
  apply: himpl_trans; first exact/Pimpl.
  apply: himpl_trans; first last.
  { apply: wp_conseq=> hv; exact/Qimpl. }
  rewrite -hsub_P -hsub_Q -fsubst_fs'Ufs.
  rewrite wp_equiv. apply (htriple_hsub g (Q:= fun v => _ \* _ \* \(m, vd)_(i <- _) _ _ v))=> //.
  { move=> ?; rewrite fsubst_fs'Ufs; exact/fC. }
  { move=> hv hv' hvE. do 2? fequal. apply/hbig_fset_eq=> i /[dup]?.
    rewrite indom_interval=> ?.
    apply/HE=> // ??; apply/hvE; rewrite indom_union_eq /Fs indom_Union.
    right; by exists i. }
  { move=> > /fGlue/[apply]-[]; rewrite ?indom_union_eq.
    split; by right. }
  rewrite -wp_equiv.
  apply/wp_for_hbig_op; first last.
  all: try eassumption.
  { by move=> ? /= /[dup]/htE<-/fid->. }
  { by rewrite /Fs disjoint_Union. }
  { reflexivity. }
  { move=> ??; exact. }
  { move=> ?; exact. }
  move=> l Q' ??.
  have/[dup]->: forall R, 
    \*_(d <- fsi' l) (fun x => hsub (R (f x)) (Gi x)) d = 
    \*_(d <- fsi' l) (fun x => hsub (R (f x)) (gi l)) d.
  { move=> ?.
    apply/hbig_fset_eq=> ??; fequals.
    rewrite (Gi_in l) // indom_interval; lia. }
  move->. rewrite -hsub_Pi // -hsub_Qi // -fsubst_fs'Ufsi ?indom_interval; last lia.
  rewrite wp_equiv.
  have vE: forall v: D-> val, v = (v \o gi l) \o fi l.
  { by move=> ?; extens=> ?; rewrite /= C1. }
  apply/htriple_conseq; [|eauto|move=> v ?; rewrite {2}(vE v); exact].
  apply (htriple_hsub (fi l) (Q := fun v => _ \* _ \* _ \(m, vd) _ (v \o _))).
  { by move=> *; rewrite C1. }
  { move=> > hvE; do 3? fequal; apply/HE=> // i ind.
    apply/hvE; rewrite indom_union_eq -fiIm indom_fsubst; right.
    by exists i. }
  { by move=> ?? /[swap]/(can_inj (C2 _)). }
  { move=> x. rewrite fsubst_fs'Ufsi ?indom_interval; last lia.
    rewrite ?indom_union_eq -fiIm indom_fsubst. 
    split=> -[].
    { move=> /[dup]/(giid l){2}<- /[! C2]; by left. }
    { move=> ?; right; by exists x. }
    { move=> /[dup]/(giid l){1}<- /[! C1]; by left. }
    case=> ? []/(can_inj (C1 _))->; by right. }
  have: forall R : _ -> hhprop,
    \*_(d <- fsi' l) R (f d) =
    \*_(d <- fsi l) R d.
  { move=> ?. rewrite -fiIm -(hstar_fset_eq _ _ (C1 _)).
    apply/hbig_fset_eq=> ? /fRestr-> //.
    rewrite indom_interval; lia. }
  move=> /[dup]->->; rewrite -wp_equiv.
  have ->:
    (fun v => Inv (l + 1) \* (\*_(d <- fsi l) R' d) \* Q' \(m, vd) H' l (v \o fi l)) = 
    fun v => Inv (l + 1) \* (\*_(d <- fsi l) R' d) \* Q' \(m, vd) H' l (v \o f).
  { apply/fun_ext_1=> ?; do 3? fequal.
    apply/HE=> // ? /= /fRestr-> //; rewrite indom_interval.
    lia. }
  erewrite wp_ht_eq; eauto=> d /=.
  rewrite indom_union_eq=> -[].
  { by move/[dup]=> /giid-> ?; rewrite ?uni_in. }
  move=> ind; rewrite ?uni_nin /=.
  { rewrite (@fRestr l) ?C2 //; first (rewrite indom_interval; lia). 
    move: ind.
    by rewrite -fiIm -{1}[d] (C2 l) (fsubst_indom _ _ (C1 _) (C2 _)). }
  { move: ind; apply/disjoint_inv_not_indom_both/fsDfsi'.
    by rewrite indom_interval; lia. }
  rewrite -(fsubst_indom _ _ (C1 l) (C2 l)) C2 fsubst_fs'_fi.
  move: ind; apply/disjoint_inv_not_indom_both/fsDfsi'.
  by rewrite indom_interval; lia.
Qed. 

End WP_for.

End For_loop.

Notation "'while' C '{' T '}'"  :=
  (While C T)
  (in custom trm at level 69,
    C, T at level 0,
    format "'[' while  C ']'  '{' '/   ' '[' T  '}' ']'") : trm_scope.

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N (trm_fun i t))
  (in custom trm at level 69,
    Z, N, i at level 0,
    format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.

Section I_didnt_come_up_with_a_name.


Context {D : Type}.

Record fset_htrm := FH {
  fs_of : fset D;
  ht_of : D -> trm;
}.

From mathcomp Require Import seq.

Local Notation HD := (labeled D).

Fixpoint fset_of (fs_hts : labSeq fset_htrm) : fset (HD) :=
  if fs_hts is (Lab i fs_ht) :: fs_hts then 
    label (Lab i (fs_of fs_ht)) \u fset_of fs_hts
  else empty.

Fixpoint fset_of' (fs_hts : seq fset_htrm) : fset D :=
  if fs_hts is fs_ht :: fs_hts then 
    fs_of fs_ht \u fset_of' fs_hts
  else empty.

Fixpoint fset_of'' (fs_hts : seq fset_htrm) : fset D :=
  match fs_hts with
  | fs_ht :: nil => fs_of fs_ht
  | fs_ht :: fs_hts =>  fs_of fs_ht \u fset_of'' fs_hts
  | _ => empty
  end.

Lemma fset_of''E : fset_of'' = fset_of'.
Proof. by extens; elim=> // ? [/=|?? /=-> //] /[! union_empty_r]. Qed.


Fixpoint htrm_of (fs_hts : labSeq fset_htrm) (ld : HD) : trm :=
  if fs_hts is (Lab i fs_ht) :: fs_hts then 
    If i = lab ld /\ indom (fs_of fs_ht) (el ld) then
      ht_of fs_ht (el ld)
    else htrm_of fs_hts ld
  else 0.

Fixpoint htrm_of' (fs_hts : seq fset_htrm) (d : D) : trm :=
  if fs_hts is fs_ht :: fs_hts then 
    If indom (fs_of fs_ht) d then
      ht_of fs_ht d
    else htrm_of' fs_hts d
  else 0.

Fixpoint htrm_of'' (fs_hts : seq fset_htrm) : D -> trm :=
  match fs_hts with 
  | fs_hts :: nil => fun x => ht_of fs_hts x
  | fs_ht :: fs_hts => fun d => 
    If indom (fs_of fs_ht) d then
        ht_of fs_ht d
      else htrm_of'' fs_hts d
  | nil => fun=> 0
  end.

Arguments htrm_of'': simpl nomatch.
Arguments htrm_of'': simpl nomatch.

Lemma htrm_of''E : forall h d, indom (fset_of' h) d -> htrm_of'' h d = htrm_of' h d.
Proof.
  elim=> //? [/= _ ?|?? + ].
  { rewrite indom_union_eq=> -[] //; by case: classicT. }
  move=> IH d /=; rewrite indom_union_eq.
  case: classicT=> [|?[]//].
  { by rewrite /htrm_of''; case: classicT. }
  move=> IN; move: (IH d); rewrite /htrm_of'' /= => -> //.
  case: classicT=> //.
Qed.

Lemma fset_of_cons fs_ht fs_hts l : 
    fset_of ((Lab l fs_ht) :: fs_hts) = 
    label (Lab l (fs_of fs_ht)) \u fset_of fs_hts.
Proof. by []. Qed.

Lemma fset_of_nil : 
    fset_of nil = empty.
Proof. by []. Qed.

Definition nwp (fs_hts : labSeq fset_htrm) Q := wp (fset_of fs_hts) (htrm_of fs_hts) Q.

Definition eld : HD -> D := @el _.
Definition eld' : labeled D -> D := @el _.

Coercion eld : HD >-> D.
Coercion eld' : labeled >-> D.

Lemma eqbxx l : lab_eqb l l = true.
Proof. by case: l=> ??; rewrite /lab_eqb Z.eqb_refl Z.eqb_refl. Qed.

Lemma lab_neqd l l' : is_true (negb (lab_eqb l' l)) -> l <> l'.
Proof. by move=> /[swap]->; rewrite eqbxx. Qed.

Lemma lab_eqbP l l' : lab_eqb l l' -> l = l'.
Proof. 
  rewrite /lab_eqb istrue_and_eq -?bool_eq_true_eq ?Z.eqb_eq=> -[].
  by case: l  l'=> ?? []??/=->->. 
Qed.

Lemma lab_eqb_sym l l' :  lab_eqb l l' = lab_eqb l' l.
Proof. by rewrite /lab_eqb Z.eqb_sym [l.2 =? _]Z.eqb_sym. Qed.

Lemma fset_htrm_label_remove_disj l fs_hts fs : 
    disjoint
      (label (Lab l fs))
      (fset_of (LibLabType.remove fs_hts l)).
Proof.
  elim: fs_hts=> //= -[]l' fs_ht fs_hts IHfs_hts.
  case: ssrbool.ifP=> /= // /lab_neqd.
  rewrite disjoint_union_eq_r; split=> //.
  apply/disjoint_of_not_indom_both=> -[]??.
  by rewrite ?indom_label_eq=> /[swap]-[]<- ? [].
Qed.

Definition lookup (s : labSeq fset_htrm) (l : labType) : labeled fset_htrm := 
  let fshts := filter (fun lt => lab_eqb (lab lt) l) s in  
  let fshts := map (fun '(Lab _ x)=> x) fshts in 
  Lab l (FH (fset_of'' fshts) (htrm_of' fshts)).

Definition lookup' (s : labSeq fset_htrm) (l : labType) : labeled fset_htrm := 
  let fshts := filter (fun lt => lab_eqb (lab lt) l) s in  
  let fshts := map (fun '(Lab _ x)=> x) fshts in 
  Lab l (FH (fset_of'' fshts) (htrm_of'' fshts)).

Lemma lookup_cons_ht x xs l d :
  indom (fs_of x) d -> 
  ht_of (el (lookup (Lab l x :: LibLabType.remove xs l) l)) d = ht_of (el (Lab l x)) d.
Proof.
  case: x=> ??/= ?.
  elim: xs=> /= [|[]??/=]; rewrite eqbxx /=.
  { rewrite /lookup /=; by case: classicT. }
  by case: classicT.
Qed.

Lemma lookup_cons_fs x xs l :
  fs_of (el (lookup (Lab l x :: LibLabType.remove xs l) l)) = fs_of x.
Proof.
  case: x=> ??/=.
  elim: xs=> /= [|[]???/=]; rewrite eqbxx /=.
  { by rew_fmap. }
  case: ssrbool.ifP=> //=.
  case: ssrbool.ifP=> //=.
Qed.
  

Lemma fset_htrm_lookup_remove l fs_hts : 
  let fs_ht := lookup fs_hts l in
  let fs    := fs_of (el fs_ht) in 
    fset_of fs_hts = 
    label (Lab l fs) \u 
    fset_of (LibLabType.remove fs_hts l).
Proof.
  move=> /=. rewrite fset_of''E.
  elim: fs_hts=> /= [|[]?? fs_hts IHfs_hts]/=.
  { rewrite label_empty. by rew_fmap. }
  rewrite lab_eqb_sym.
  case: ssrbool.ifP=> /= [/lab_eqbP<-|/ssrbool.negbT/lab_neqd ?].
  { by rewrite label_union union_assoc -IHfs_hts. }
  rewrite IHfs_hts -?union_assoc [label _ \u label _]union_comm_of_disjoint //.
  apply/disjoint_of_not_indom_both=> -[??]/[swap]. 
  by rewrite ?indom_label_eq=> -[<-]_[].
Qed.

Lemma lookup_eq l fs_hts (d : HD) : 
  let fs_ht := lookup fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    indom (label (Lab l fs)) d ->
      htrm_of fs_hts d = ht d.
Proof.
  case: d=> ld d /=; rewrite indom_label_eq fset_of''E=> -[]<-. 
  elim: fs_hts=> // -[]/=?? fs_hts IHfs_hts.
  case: ssrbool.ifP=> /= [/lab_eqbP->|/ssrbool.negbT/lab_neqd ?].
  { rewrite indom_union_eq; case: classicT=> [[]_+_|/[swap]-[?[]|]//].
    { by case:classicT. }
    by case: classicT=> [??[]//|] ? /IHfs_hts. }
  case: classicT=> // -[]?; by subst.
Qed.

Lemma remove_eq l fs_hts (d : HD) : 
  let fs_ht := lookup fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    indom (fset_of (LibLabType.remove fs_hts l)) d ->
      htrm_of fs_hts d = htrm_of (LibLabType.remove fs_hts l) d.
Proof.
  move=> fs_ht fs ht.
  move/(@disjoint_inv_not_indom_both _ _ _ _ _): (fset_htrm_label_remove_disj l fs_hts fs).
  move/[apply]; rewrite {}/fs {}/ht {}/fs_ht /= -/(not _).
  case: d=> ld d /=; rewrite indom_label_eq not_and_eq fset_of''E.
  elim: fs_hts=> // -[]/=?? fs_hts IHfs_hts.
  case: ssrbool.ifP=> /= [/lab_eqbP->|/ssrbool.negbT/lab_neqd ?].
  { rewrite indom_union_eq not_or_eq.
    have->: forall A B C, A \/ B /\ C <-> (A \/ B) /\ (A \/ C) by autos*.
    case=> /[swap]/IHfs_hts; case: classicT; autos*. }
  case: classicT; autos*.
Qed.

Lemma indom_label l (fs : fset D) l' x :
  indom (label (Lab l fs)) (Lab l' x) -> l' = l.
Proof. rewrite* @indom_label_eq. Qed.

Lemma indom_remove l fs_hts l' x :
  indom (fset_of (LibLabType.remove fs_hts l)) (Lab l' x) -> l' <> l.
Proof.
  move=> /[swap]->.
  have: (indom (label (Lab l (single x tt))) (Lab l x)).
  { by rewrite label_single indom_single_eq. }
  exact/disjoint_inv_not_indom_both/fset_htrm_label_remove_disj.
Qed.

Declare Scope fset_scope.
Delimit Scope fset_scope with fs.
Declare Scope fs_hts.
Delimit Scope fs_hts with fh.

Declare Scope fun_scope.
Delimit Scope fun_scope with fn.

Notation "'⟨' l ',' x '⟩'" := (label (Lab l%Z x%fs)) (at level 5, right associativity, format "⟨ l ,  x ⟩").

Definition ntriple H fs_hts Q := H ==> nwp fs_hts Q.

Local Notation hhprop := (hhprop HD).

Lemma xfocus_lemma (l : labType) fs_hts (Q : (HD -> val) -> hhprop) H : 
  let fs_ht := lookup' fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    H ==> wp ⟨l, fs⟩ [eta ht]
            (fun hr => nwp (LibLabType.remove fs_hts l) (fun hr' => Q (hr \u_⟨l, fs⟩ hr'))) ->
    ntriple H fs_hts Q.
Proof.
  move=> fs_ht fs ht.
  rewrite (@wp_ht_eq HD ⟨l, fs⟩ _ (ht_of (el (lookup fs_hts l)))).
  { apply: himpl_trans_r.
    rewrite /nwp (fset_htrm_lookup_remove l fs_hts) -wp_union -/fs_ht; first last.
    { exact/fset_htrm_label_remove_disj. }
    under (wp_ht_eq (htrm_of fs_hts))=> ? IN.
    { rewrite (lookup_eq _ _ IN); over. }
    rewrite -/fs_ht -/ht.
    apply/wp_conseq=> hv.
    under (wp_ht_eq (htrm_of fs_hts))=> ? IN.
    { rewrite (remove_eq _ _ IN); over. }
    move=> h Hwp; rewrite -/fs //. }
  case=> ?? /[! @indom_label_eq]-[<-].
  rewrite /fs/ht/fs_ht/lookup/lookup'/= fset_of''E.
  exact/htrm_of''E.
Qed.

Lemma disjoint_eq_label {T} (l : labType) (fs1 fs2 : fset T) : 
  disjoint (label (Lab l fs1)) (label (Lab l fs2)) <-> disjoint fs1 fs2.
Proof.
  split.
  { move/(@disjoint_inv_not_indom_both _ _ _ _ _)=> dj.
    apply/disjoint_of_not_indom_both=> x in1 in2.
    by apply/(dj (Lab l x)); rewrite indom_label_eq. }
  move/(@disjoint_inv_not_indom_both _ _ _ _ _)=> dj.
  apply/disjoint_of_not_indom_both=> -[??].
  by rewrite ?indom_label_eq=> -[_]/[swap]-[_]/dj/[apply].
Qed.

Lemma disjoint_subset {A} (fs1 fs2 fs : fset A) : 
  disjoint fs1 fs2 -> 
  (forall x, indom fs x -> indom fs1 x) -> 
  disjoint fs fs2.
Proof.
  move/(@disjoint_inv_not_indom_both _ _ _ _ _)=> dj ind.
  apply/disjoint_of_not_indom_both=> ? /ind; eauto.
Qed.

Arguments disjoint_subset {_} _.

Lemma xfocus_pred_lemma (p : D -> Prop) (l : labType) fs_hts (Q : (HD -> val) -> hhprop) H : 
  let fs_ht := lookup' fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    H ==> wp ⟨l, fs ∖ p⟩ [eta ht]
            (fun hr => nwp (Lab l (FH (fs ∩ p) ht) :: LibLabType.remove fs_hts l) (fun hr' => Q (hr \u_⟨l, fs ∖ p⟩ hr'))) ->
    ntriple H fs_hts Q.
Proof.
  move=> fs_ht fs ht.
  have sb: forall x P, indom ⟨l, intr fs P⟩ x -> indom ⟨l, fs⟩ x.
  { case=> ???; by rewrite ?indom_label_eq intr_indom_both=> -[->][]. }
  rewrite (@wp_ht_eq HD _ _ (ht_of (el (lookup fs_hts l)))).
  { apply: himpl_trans_r.
    rewrite /nwp (fset_htrm_lookup_remove l fs_hts) -/fs_ht -/fs. 
    rewrite fset_of_cons /fs_of /=.
    rewrite (wp_ht_eq (fun _ => htrm_of' _ _) (htrm_of fs_hts)).
    { set (Fs := (⟨_,_⟩ \u _)).
      set (Fn := (fun ld => If _ then _ else _)).
      have->: wp Fs Fn = wp Fs (htrm_of fs_hts).
      { apply/fun_ext_1=> ?; apply/wp_ht_eq.
        rewrite /Fs/Fn=> -[l' x] /=.
        case: classicT.
        { case=><- IN ?; rewrite /ht /fs_ht (lookup_eq l) //.
          { rewrite /lookup/lookup' /=.
            rewrite htrm_of''E // -fset_of''E.
            move: IN; rewrite /fs /fs_ht /lookup' /=.
            rewrite intr_indom_both; autos*. }
          apply/sb; rewrite indom_label_eq; eauto. }
        rewrite indom_union_eq=> /[swap]-[].
        { by rewrite indom_label_eq=> -[->]?[]. }
        by move/remove_eq->. }
      rewrite wp_union.
      { rewrite /Fs -union_assoc -label_union.
        rewrite [(_ ∖ _) \u _]union_comm_of_disjoint ?fs_pred_part //.
        rewrite disjoint_comm; exact/fs_pred_part_disj. }
      rewrite /Fs disjoint_union_eq_r disjoint_eq_label; split.
      { rewrite disjoint_comm; exact/fs_pred_part_disj. }
      apply/(disjoint_subset ⟨l, fs⟩); eauto.
      exact/fset_htrm_label_remove_disj. }
    by move=> ? /sb/lookup_eq ->. }
  case=>l' d  /sb; rewrite indom_label_eq=> -[<-]?. 
  by rewrite /ht/lookup/fs_ht/lookup' /= htrm_of''E // -fset_of''E.
Qed.

Definition uni_pred {A B} (f g : A -> B) (p : A -> Prop) := 
  fun x => If p x then f x else g x.

Lemma xfocus_pred_lemma' (p : D -> Prop) (l : labType) fs_hts (Q : (HD -> val) -> hhprop) H : 
  let fs_ht := lookup' fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    H ==> wp ⟨l, fs ∖ p⟩ [eta ht]
            (fun hr => 
              nwp (Lab l (FH (fs ∩ p) ht) :: LibLabType.remove fs_hts l) 
                (fun hr' => Q (lab_fun_upd (uni_pred hr' hr p) hr' l))) ->
    ntriple H fs_hts Q.
Proof.
  move=> fs_ht fs ht Impl.
  apply/(@xfocus_pred_lemma p l). rewrite -/fs_ht -/fs -/ht.
  apply: himpl_trans; eauto. apply/wp_conseq=> hr.
  apply: himpl_trans; first last.
  { apply/wp_hv. } 
  rewrite -/(nwp _ _); apply/wp_conseq=> hr'.
  xsimpl (lab_fun_upd (uni_pred hr' hr p) hr' l)=> ?.
  apply:applys_eq_init; fequals; extens=> -[l' x].
  case: (classicT (l' = l))=>[->|?].
  { rewrite /uni_pred /= /lab_fun_upd /= eqbxx.
    case: classicT=> px.
    { rewrite uni_nin.
      { rewrite /uni; do ? case: classicT=> //=.
        by rewrite eqbxx. }
      rewrite indom_label_eq intr_indom_both /=. autos*. }
    rewrite /uni; case: classicT=> // ?.
    case: classicT=> //=.
    { rewrite indom_union_eq indom_label_eq intr_indom_both=> -[]; autos*.
      by move/indom_remove. }
    rewrite ?eqbxx; by case: classicT. }
  rewrite /= -?/(lab_fun_upd _ _ _ _) -?/(lab_fun_upd _ _ _).
  rewrite lab_fun_upd_neq; eauto.
  rewrite /uni; case: classicT=> [/indom_label?|]; first by subst.
  case: classicT=> //; rewrite lab_fun_upd_neq //.
Qed.


Arguments htrm_of : simpl never.

Lemma xunfocus_lemma (Q : (HD -> val) (*-> (HD -> val)*) -> hhprop) fs_hts 
  (ht : D -> trm) (fs : fset D) H (ht' : HD -> _)
  (Q' : (HD -> val) -> (HD -> val) -> hhprop)
  (l : labType) :
  ~ has_lab fs_hts l ->
  (ht = (fun d => ht' (Lab l d))) ->
  (forall hr hr', Q' hr hr' = Q (hr \u_⟨l, fs⟩ hr')) ->
  (* adequate (fun hr => Q hr hr) (⟨l, fs⟩ \u fset_of fs_hts) -> *)
  ntriple H ((Lab l (FH fs ht)) :: fs_hts) (fun hr => Q hr) ->
  H ==> wp ⟨l, fs⟩ ht' (fun hr => nwp fs_hts (fun hr' => Q' hr hr')).
Proof.
  rewrite /ntriple/nwp=> /hasnt_lab /[dup]rE {1}-> /[! fset_of_cons] htE QE.
  apply: himpl_trans_r.
  rewrite -wp_union /=; first last.
  {  exact/fset_htrm_label_remove_disj. }
  under wp_ht_eq=> -[l' d] IN.
  { unfold label in IN. rewrite -> indom_Union in IN. 
    setoid_rewrite -> indom_single_eq in IN.
    simpl in IN.
    destruct IN as (? & ? & IN). injection IN as <-. subst.
    rewrite (@lookup_eq l) rE ?lookup_cons // ?lookup_cons_ht ?lookup_cons_fs //=. 
    { rewrite rE. over. }
    unfold label. rewrite -> indom_Union. eauto. } 
  move=> /= h Hwp; simpl; apply/wp_conseq; eauto=> hr /=; simpl.
  under wp_ht_eq=> ? IN.
  { rewrite (@remove_eq l) /= eqbxx /= // -rE; over. }
  rewrite -rE // => {Hwp}h Hwp.
  eapply wp_conseq; last exact/Hwp.
  by move=> ??; rewrite QE.
Qed.

Lemma nwp0 Q : 
  nwp nil (fun=> Q) = Q.
Proof. by rewrite /nwp fset_of_nil wp0. Qed.

Lemma xcleanup_lemma fs_hts Q v l fs H Q' : 
  ~ has_lab fs_hts l ->
  (forall hr, Q' hr = Q (v \u_⟨l, fs⟩ hr)) ->
  ntriple H fs_hts (fun hr => Q (lab_fun_upd v hr l)) -> 
  H ==> nwp fs_hts (fun hr => Q' hr).
Proof.
  move=> /hasnt_lab-> QE.
  apply: himpl_trans_r; rewrite /nwp.
  move=> ? Hwp; apply/wp_hv; apply: wp_conseq Hwp=> hr ? Qh.
  exists (lab_fun_upd v hr l); rewrite QE.
  move: Qh; apply: applys_eq_init; fequals; apply/fun_ext_1=> -[l' ?].
  rewrite /uni; case: classicT=> [/indom_label->|].
  { by rewrite /lab_fun_upd eqbxx. }
  case: classicT=> // /indom_remove *. 
  rewrite lab_fun_upd_neq //.
Qed.

Lemma hbig_fset_label_single' {DD A} (Q : DD -> LibSepReference.hhprop A) (d : DD) :
  \*_(d0 <- single d tt) Q d0 = Q d.
Proof using.
  unfold hbig_fset.
  rewrite -> update_empty. rewrite -> (snd (@fset_foldE _ _ _ _)); auto.
  2: intros; xsimpl.
  rewrite -> (fst (@fset_foldE _ _ _ _)); auto.
Qed.

Lemma hstar_fset_Lab (Q : labeled D -> hhprop) l fs : 
  \*_(d <- ⟨l, fs⟩) Q d = 
  \*_(d <- fs) (Q (Lab l d)).
Proof.
  elim/fset_ind: fs. 
  { by rewrite label_empty ?hbig_fset_empty. }
  move=> fs x IHfs ?.
  rewrite label_update ?hbig_fset_update // ?indom_label_eq ?IHfs//.
  by case.
Qed.
Hint Rewrite @hbig_fset_label_single' @hstar_fset_Lab : hstar_fset.


Lemma lhtriple_ref : forall (f : val)  l x, 
  htriple ⟨l, (single x tt)⟩ (fun d => val_ref f)
    (\[] : hhprop)
    (fun hr => (\exists (p : loc), \[hr = fun=> val_loc p] \*  p ~(Lab l x)~> f)).
Proof using.
move=> ? l d. rewrite -wp_equiv; apply:himpl_trans; last apply/wp_hv.
simpl; rewrite wp_equiv; apply/htriple_conseq; first apply/htriple_ref. 
{ xsimpl*. }
move=> ?. xpull=> p->. 
xsimpl ((fun=> val_loc (p (Lab l d))) : HD -> _) (p (Lab l d)).
extens=> -[]??; rewrite /uni; case: classicT=> //.
by rewrite indom_label_eq indom_single_eq=> -[]<-<-.
Qed.

Lemma lhtriple_get : forall v (p : loc) fs,
  @htriple D fs (fun d => val_get p)
    (\*_(d <- fs) p ~(d)~> v)
    (fun hr => \[hr = fun => v] \* (\*_(d <- fs) p ~(d)~> v)).
Proof using.
  intros. unfold htriple. intros H'. applys @hhoare_conseq @hhoare_get; xsimpl~.
Qed.

Lemma lhtriple_set : forall v (w : _ -> val) (p : loc) fs,
  @htriple D fs (fun d => val_set p (w d))
  (\*_(d <- fs) p ~(d)~> v)
  (fun hr => \[hr = fun=> val_unit] \* (\*_(d <- fs) p ~(d)~> w d)).
Proof using.
intros. unfold htriple. intros H'. applys @hhoare_conseq @hhoare_set; xsimpl*.
Qed.

Lemma lhtriple_free : forall (p : loc) (v : val) fs,
  @htriple D fs (fun d => val_free p)
    (\*_(d <- fs) p ~(d)~> v)
    (fun _ => \[]).
Proof using. intros. apply htriple_free. Qed.

Hint Resolve (*htriple_ref_lab*) lhtriple_ref lhtriple_get lhtriple_set lhtriple_free : lhtriple.

Arguments xfocus_lemma _ {_}.
Arguments xunfocus_lemma _ {_}.

Lemma xnwp0_lemma H Q :
  H ==> Q ->
  ntriple H nil (fun=> Q).
Proof.
  by apply: himpl_trans_r=> ? /[! nwp0].
Qed.

Lemma xnwp1_lemma fs_ht l :
  wp (label (Lab l (fs_of fs_ht))) (ht_of fs_ht) =
  nwp ((Lab l fs_ht) :: nil).
Proof.
  apply/fun_ext_1=> ?.
  rewrite /nwp /= union_empty_r /htrm_of /=.
  erewrite wp_ht_eq; first eauto.
  case=> ??; rewrite indom_label_eq=> -[<-] /=.
  case: classicT; autos*.
Qed.

Lemma xntriple1_lemma H Q fs_ht l :
  H ==> wp (label (Lab l (fs_of fs_ht))) (ht_of fs_ht) Q =
  ntriple H ((Lab l fs_ht) :: nil) Q.
Proof. by rewrite /ntriple xnwp1_lemma. Qed.

Lemma nwp_of_ntriple H Q fs_hts :
  ntriple H fs_hts Q =
  H ==> nwp fs_hts Q.
Proof. by []. Qed.

Lemma ntriple_conseq_frame H2 H1 H Q fs_ht:
  ntriple H1 fs_ht (Q \*+ \Top) ->
  H ==> H1 \* H2 -> ntriple H fs_ht (Q \*+ \Top).
  move=> T Impl; rewrite /ntriple/nwp wp_equiv.
  apply/htriple_conseq_frame; eauto.
  { rewrite* <-@wp_equiv. }
  xsimpl*.
Qed.

Lemma ntriple_conseq_frame2 H2 H1 Q1 H Q fs_ht : 
  ntriple H1 fs_ht Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q -> ntriple H fs_ht Q.
Proof.
  rewrite /ntriple /nwp ?wp_equiv=> *.
  apply/htriple_conseq_frame; eauto.
Qed.

Lemma ntriple_conseq H1 Q1 H Q fs_ht : 
  ntriple H1 fs_ht Q1 ->
  H ==> H1 ->
  Q1 ===> Q -> ntriple H fs_ht Q.
Proof.
  rewrite /ntriple /nwp ?wp_equiv=> *.
  apply/htriple_conseq; eauto.
Qed.

Lemma ntriple_frame X H Q fs_ht H' Q' : 
  (H = H' X) ->
  (forall v, Q v = Q' X v) ->
  (H' X ==> (H' hempty) \* X) ->
  ((Q' \[]) \*+ X ===> Q' X) ->
  H' \[] ==> nwp fs_ht (fun v => Q' \[] v) ->
  ntriple H fs_ht Q.
Proof.
move=>-> QE ? QI ?.
apply/ntriple_conseq_frame2; eauto=> hv; rewrite* QE.
Qed.

Fact hstar0E : hstar \[] = @id hhprop.
Proof. apply/fun_ext_1=>?. by rewrite hstar_hempty_l. Qed.

Lemma hstar_fset_label_single {A : Type} (x : A) : 
@hbig_fset D _ hstar (single x tt) = @^~ x.
Proof. 
  apply/fun_ext_1=> ?.
  rewrite update_empty hbig_fset_update // hbig_fset_empty. xsimpl*. 
Qed.
Fact hstar_interval_offset (L R offset : int) (f : int -> hhprop) :
  \*_(d <- interval L R) f (d + offset) = 
  \*_(d <- interval (L + offset) (R + offset)) f d.
Proof.
  rewrite <- interval_fsubst_offset.
  rewrite <- hstar_fset_eq with (g:=fun i => i - offset); try reflexivity.
  hnf. intros. lia.
Qed.


End I_didnt_come_up_with_a_name.

Declare Scope fset_scope.
Delimit Scope fset_scope with fs.
Declare Scope fs_hts.
Delimit Scope fs_hts with fh.

Declare Scope fun_scope.
Delimit Scope fun_scope with fn.

Notation "'⟨' l ',' x '⟩'" := (label (Lab l%Z x%fs)) (at level 5, right associativity, format "⟨ l ,  x ⟩").

Arguments disjoint_subset {_} _.

Arguments htrm_of : simpl never.

Hint Resolve (*htriple_ref_lab*) lhtriple_ref lhtriple_get lhtriple_set lhtriple_free : lhtriple.

Arguments xfocus_lemma _ {_}.
Arguments xunfocus_lemma _ {_}.

Notation "'N-WP' fs_hts '{{' v ',' Q '}}'" := 
    (nwp 
      fs_hts%fh
      (fun v => Q%fn)) (at level 20, v name,
      format "'N-WP'  '[' fs_hts '/'  '{{'  v ','  Q  '}}' ']' ") 
    : wp_scope.

Notation "'{{' H '}}' fs_hts '{{' v ',' Q '}}'" := 
    (ntriple 
      H%fn
      fs_hts%fh
      (fun v => Q%fn)) (at level 20, v name,
      format " '[' '[' '{{'  H  '}}' ']' '/   ' '[' fs_hts ']' '/' '[' '{{'  v ','  Q  '}}' ']' ']' ") 
    : wp_scope.

Notation "'[{' fs1 ';' fs2 ';' .. ';' fsn '}]'" := 
  (cons fs1%fh (cons fs2%fh .. (cons fsn%fh nil) ..)) (at level 30
  , format "[{ '['  fs1 ';' '//'  fs2 ';' '//'  .. ';' '//'  fsn  ']' }] "
  ) : fs_hts.

Notation "'[{' fs '}]'" := 
  (cons fs%fh nil) (at level 30, format "[{  fs  }]") : fs_hts.

Export ProgramSyntax.

Notation "'[' l '|' d 'in' fs '=>' t ]" := (Lab (l,0)%Z (FH fs%fs (fun d => t))) 
  (at level 20, t custom trm at level 100, d name) : fs_hts.

Notation "'{' l '|' d 'in' fs '=>' t }" := (Lab (l,0)%Z (FH fs%fs (fun d => t))) 
  (at level 20, d name, only parsing) : fs_hts.

Tactic Notation "xfocus" constr(S) := 
  let n := constr:(S) in
  apply (@xfocus_lemma _ n); simpl; try apply xnwp0_lemma.

Tactic Notation "xfocus" constr(S) constr(P) := 
  let n := constr:(S) in
  let P := constr:(P) in
  apply (@xfocus_pred_lemma' _ P (n,0)%Z); simpl; rewrite /uni_pred /=; rewrite -?xntriple1_lemma; try apply xnwp0_lemma.

Tactic Notation "xfocus_split_core" constr(HPP) constr(S) constr(P) :=
  repeat match HPP with
  | context[hbig_fset _ ?ffs ?ff] =>
    match ffs with
    | context[intr _ _] => fail
    | _ =>
      match ff with
      | context[Lab (S,0)%Z] => rewrite -> (fun_eq_1 ff (hbig_fset_part ffs P)) in |- *
      end
    end
  end.

Tactic Notation "xfocus_split" constr(S) constr(P) :=
  match goal with
  | |- (?HPP ==> _) => xfocus_split_core HPP S P
  | |- (ntriple ?HPP _ _) => xfocus_split_core HPP S P
  end.

Tactic Notation "xfocus" "*" constr(S) constr(P) := 
  xfocus S P; xfocus_split S P.

Tactic Notation "xframe" constr(H) := 
  let h := constr:(H) in
  eapply (@ntriple_conseq_frame _ h (protect _)); [|xsimpl]; rewrite /protect; eauto.

Tactic Notation "xunfocus" := 
eapply xunfocus_lemma=> //=; [intros; remember ((_ \u_ _) _); reflexivity|]=>/=.

Tactic Notation "xcleanup" constr(n) := 
match goal with 
| |- context G [?v \u_ ⟨_, ?fs⟩] => eapply ((@xcleanup_lemma _ _ _ v (n,0)%Z fs))
end=>//; [intros; remember ((_ \u_ _) _); reflexivity|].


Tactic Notation "xin" constr(S1) ":" tactic(tac) := 
  let n := constr:(S1) in
  xfocus (n, 0)%Z; tac; try(
  first [xunfocus | xcleanup n]; simpl; try apply xnwp0_lemma); rewrite -?xntriple1_lemma /=.


Tactic Notation "xin" constr(S1) constr(S2) ":" tactic(tac) := 
  let n1 := eval vm_compute in (Z.to_nat S1) in
  let n2 := eval vm_compute in (Z.to_nat S2) in
  xfocus n1; tac; first [xunfocus | xcleanup n1];
  xfocus n2; tac; first [xunfocus | xcleanup n2]; simpl; try apply xnwp0_lemma.

Tactic Notation "xnsimpl" := 
  rewrite /ntriple; xsimpl; try first [ setoid_rewrite <-nwp_of_ntriple| rewrite -nwp_of_ntriple].

Notation "f '[`' i '](' j ')'" := (f (Lab (i,0)%Z j)) (at level 30, format "f [` i ]( j )") : fun_scope.
Notation "'⟨' l ',' x '⟩'" := ((Lab l%Z x%fs)) (at level 5, right associativity, format "⟨ l ,  x ⟩") : arr_scope.

Global Hint Rewrite @hstar_fset_label_single @hstar_fset_Lab : hstar_fset.

Arguments lab_fun_upd /.

Global Arguments ntriple_frame _ {_}.

Tactic Notation "xframe2" uconstr(QH) := 
  (try (xframe QH; [ ]));
  try (
    let Q := fresh "Q" in 
    let HEQ := fresh "Q" in 
    remember QH as Q eqn: HEQ in |- *;
    rewrite -?HEQ;
    eapply (@ntriple_frame _ Q); 
    [ let h := fresh "h" in 
      let f := fresh "h" in 
      match goal with |- ?x = ?y => set (h := x) end;
      pattern Q in h;
      set (f := fun _ => _) in h;
      simpl in h;
      rewrite /h;
      reflexivity
    | let h := fresh "h" in 
      let f := fresh "h" in 
      let v := fresh "h" in 
      intros v; 
      match goal with |- ?x = ?y => set (h := x) end;
      pattern Q, v in h;
      set (f := fun _ _ => _) in h;
      simpl in h;
      rewrite /h;
      reflexivity
    | simpl; try rewrite HEQ; xsimpl*
    | simpl=> ?;
      try (have->: forall f, (fun x : hheap _ => f x) = f by []);
      try (have->: forall f, (fun x : hheap D => f x) = f by []);
      try rewrite HEQ;
      xsimpl*
    | simpl; rewrite -> ?hstar0E
    ]; clear Q HEQ
  ).

Tactic Notation "xcleanup_unused" := 
  (repeat let HH := fresh "uselessheap" in set (HH := hbig_fset hstar (_ ∖ _) _); xframe2 HH; clear HH).

Tactic Notation "xcleanup_unused" "*" :=
  rewrite -> ! hbig_fset_hstar; xcleanup_unused; rewrite -!hbig_fset_hstar; xsimpl.

Tactic Notation "xdrain_unused" := 
  (repeat let HH := fresh "uselessheap" in set (HH := hbig_fset hstar (_ ∖ _) _); xframe HH; clear HH).

Tactic Notation "xdrain_unused" "*" :=
  rewrite -> ! hbig_fset_hstar; xdrain_unused; rewrite -!hbig_fset_hstar.

Tactic Notation "xclean_heap_core" constr(Q) :=
  match Q with
  | context[htop] => xdrain_unused
  | _ => try xcleanup_unused
  end.

Tactic Notation "xclean_heap" := 
  match goal with
  | |- (himpl _ (nwp _ ?Q)) => xclean_heap_core Q
  | |- (ntriple _ _ ?Q) => xclean_heap_core Q
  end.

Arguments wp_for _ _ {_}.

Arguments disjoint_inv_not_indom_both {_ _ _ _ _}.

Lemma disjoint_single {T} (x y : T) : 
  disjoint (single x tt) (single y tt) = (x <> y).
Proof.
  extens; split; last apply/disjoint_single_single.
  move/[swap]->; exact/disjoint_single_single_same_inv.
Qed.

Lemma disjoint_interval (x1 y1 x2 y2 : int) : 
  disjoint (interval x1 y1) (interval x2 y2) = ((y1 <= x2) \/ (y2 <= x1) \/ (y1 <= x1) \/ (y2 <= x2)).
Proof.
  extens; split=> [/(@disjoint_inv_not_indom_both _ _ _ _ _)|].
  { setoid_rewrite indom_interval=> /[dup]/(_ x1)+/(_ x2).
   lia. }
  move=> H; apply/disjoint_of_not_indom_both=> ?; rewrite ?indom_interval.
  move: H; lia.
Qed.

Lemma disjoint_single_interval (x1 y1 x : int) : 
  disjoint (single x tt) (interval x1 y1) = ((x < x1) \/ (y1 <= x)).
Proof.
  extens; split=> [/(@disjoint_inv_not_indom_both _ _ _ _ _)|].
  { move=> /[dup]/(_ x); rewrite indom_interval indom_single_eq.
    lia. }
  move=> H; apply/disjoint_single_of_not_indom.
  rewrite indom_interval. math.
Qed.


Lemma disjoint_interval_single (x1 y1 x : int) : 
  disjoint (interval x1 y1) (single x tt) = ((x < x1) \/ (y1 <= x)).
Proof. by rewrite disjoint_comm disjoint_single_interval. Qed.

Lemma disjoint_label {T} (l l' : labType) (fs1 fs2 : fset T) : 
  disjoint (label (Lab l fs1)) (label (Lab l' fs2)) = ((l <> l') \/ disjoint fs1 fs2).
Proof.
  extens; split=> [/(@disjoint_inv_not_indom_both _ _ _ _ _)|].
  { move=> IN; case: (classicT (l = l')); [right|left]=> //; subst.
    apply/disjoint_of_not_indom_both=> x.
    move: (IN (Lab l' x)); rewrite ?indom_label_eq; autos*. }
  case: (classicT (l = l'))=> [<-|? _].
  { rewrite*  @disjoint_eq_label. }
  apply/disjoint_of_not_indom_both=> -[??]; rewrite ?indom_label_eq.
  case=><-; autos*.
Qed.

Lemma disjoint_prod {A B : Type} (fs1 fs2 : fset A) (fr1 fr2 : fset B): 
  disjoint (fs1 \x fr1) (fs2 \x fr2) = (disjoint fs1 fs2 \/ disjoint fr1 fr2).
Proof.
  extens; splits.
  { move/disjoint_inv_not_indom_both=> Dj.
    case: (prop_inv (disjoint fs1 fs2)); autos*.
    move=> NDj; right; apply/disjoint_of_not_indom_both=> x ??.
    have: ~ (forall p : A, indom (fs1) p -> indom (fs2) p -> False).
    { by move=> ?; apply/NDj/disjoint_of_not_indom_both. }
    rewrite not_forall_eq=> -[]y IN.
    apply/(Dj (y,x)); rewrite indom_prod=> /=; splits=>//.
    all: apply:not_not_inv=> ?; apply/IN; autos*. }
  case=> /disjoint_inv_not_indom_both=> Dj.
  all: apply/disjoint_of_not_indom_both=> -[]??; rewrite ?indom_prod/=; autos*.
Qed.

Global Hint Rewrite @disjoint_single disjoint_interval disjoint_single_interval 
  disjoint_interval_single @disjoint_eq_label @disjoint_label @disjoint_prod : disjointE.

Global Hint Rewrite @indom_label_eq @indom_union_eq @indom_prod @indom_interval @indom_single_eq @intr_indom @intr_neg_indom @indom_Union : indomE.

Ltac indomE := autorewrite with indomE.

Ltac disjointE := 
  let Neq := fresh in
  let i   := fresh "i" in
  let j   := fresh "j" in 
  try intros i j; 
  indomE;
  autorewrite with disjointE; try lia; try eqsolve.

Definition Get {A} Z N (fsi : int -> fset A) (x : A)  :=
  match classicT (exists i, indom (interval Z N) i /\ indom (fsi i) x) with 
  | left P => 
    let '(@exist _ _ a _) := indefinite_description P in a
  | _ => 0
  end.

Lemma Get_in {A} Z N i x (fsi : int -> fset A) : 
  Z <= i < N ->
  indom (fsi i) x ->
    indom (fsi (Get Z N fsi x)) x /\ 
    indom (interval Z N) (Get Z N fsi x).
Proof.
  move=> ??; rewrite /Get; case: classicT=> [?|[] ].
  { case: (indefinite_description _)=> j [] ? //. }
  by exists i; rewrite indom_interval.
Qed.

Definition set2 D y : labeled D -> labeled D :=
  fun '(Lab (p, q) x) => Lab (p, y) x.

Arguments el {_}.

Lemma xfor_lemma D `{ID : Inhab (labeled D)}
  Inv 
  (R R' : D -> hhprop (labeled D))
  m vd (H : int -> hhprop (labeled D)) (H' : int -> (labeled D -> val) -> hhprop(labeled D) )
  s fsi1 vr
  (N: Z) (C1 : D -> trm) (C : trm)
  (i j : Z)
  Pre Post: 
  (forall (l : int) Q, 
    (0 <= l < N) ->
    {{ Inv l \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R (el d)) \* 
        Q \(m, vd) H l }}
      [{
        {i| _  in single s tt  => subst vr l C};
        {j| ld in fsi1 l       => C1 ld}
      }]
    {{ v, 
        Inv (l + 1) \* 
        (\*_(d <- ⟨(j,0)%Z, fsi1 l⟩) R' (el d)) \* 
        Q \(m, vd) H' l v }}) ->
  (forall j : int, hlocal (Inv j) ⟨(i,0%Z), single s tt⟩) ->
  (forall j : int, hlocal (H j) ⟨(i,0%Z), single s tt⟩) ->
  (forall (j : int) (v : labeled D -> val), hlocal (H' j v) ⟨(i,0%Z), single s tt⟩) ->
  (forall i : D, hlocal (R i) ⟨(j,0%Z), single i tt⟩) ->
  (forall i : D, hlocal (R' i) ⟨(j,0%Z), single i tt⟩) ->
  (forall (hv hv' : labeled D -> val) (m : int),
    (0 <= m < N) ->
    (forall i, indom (fsi1 m) i -> hv[`j](i) = hv'[`j](i)) ->
    H' m hv = H' m hv') ->
  comm m -> assoc m ->
  (forall x y, (vd x /\ vd y) <-> vd (m x y)) ->
  (i <> j)%Z ->
  0 <= N ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> 
    Inv 0 \* 
    (\*_(d <- Union (interval 0 N) fsi1) R d) \*
    \(m, vd)_(i <- interval 0 N) H i) ->
  (forall hv, 
    Inv N \* 
    (\*_(d <- Union (interval 0 N) fsi1) R' d) \* 
    (\(m, vd)_(i <- interval 0 N) H' i hv) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      {i| _  in single s tt => For 0 N (trm_fun vr C)};
      {j| ld in Union (interval 0 N) fsi1 => C1 ld}
    }]
  {{ v, Post v }}.
Proof.
  move=> IH lI lH lH' lR lR' opP CM AS VM iNj N0 ? ??? ?? PreH PostH.
  rewrite /ntriple /nwp ?fset_of_cons /= union_empty_r.
  set (f := (fun '(Lab (p, q) x) => Lab 
    (If p = j then 
      If  0 <= q < N /\ indom (fsi1 q) x then (j,0)%Z else (p, 2 * (q + N) + 1)
    else (p, q)) 
    x) : labeled D -> labeled D).
  set (g := (fun '(Lab (p, q) x) => Lab 
    (If p = j then 
      If q = 0 /\ indom (Union (interval 0 N) fsi1) x then
        (j, Get 0 N fsi1 x)
      else (j, -1)
    else (p, q)) x)).
  set (fi (i : int) := (fun '(Lab (p, q) x) => If p = j then Lab (j, q - i) x else Lab (p, q) x) : labeled D -> labeled D).
  set (gi (i : int) := (fun '(Lab (p, q) x) => If p = j then Lab (j, q + i) x else Lab (p, q) x) : labeled D -> labeled D).
  set (fsi' (i : int) := ⟨(j, i), fsi1 i⟩).
  have H'E :forall hv, 
    \(m, vd)_(i <- interval 0 N) H' i hv = \(m, vd)_(i <- interval 0 N) H' i (hv \o f \o set2 i).
  { move=> hv; apply/hbig_fset_eq=> d. rewrite indom_interval=> ?.
    apply/opP=> // x ? /=; case: classicT=> // _.
    by case: classicT=> // -[]; split=> //. }
  set (r := fun x => if lab_eqb (lab x) (j,0) then R (el x) else \[]).
  set (r' := fun x => if lab_eqb (lab x) (j,0) then R' (el x) else \[]).
  apply/(
    wp_for_hbig_op_na_bis Inv (r) (r') H (fun i hv => H' i (hv \o set2 i))  
      (fun d => ⟨(j,0%Z), fsi1 d⟩) Post fsi' fi gi g
      (fs' := ⟨(i, 0), single s tt⟩)
      (f := f)
      (* (fsi' := fsi') *)
  ); try eassumption.
  { rewrite -Union_label /r/r' . xsimpl*; rewrite eqbxx //. }
  { by rewrite -Union_label. }
  { by case=> l d; rewrite indom_label_eq /= /htrm_of; case: classicT. }
  { by move=> *. }
  { case=> [??]; rewrite /r; case: ssrbool.ifP=> // [|?]. 
    { by move=> /= /lab_eqbP->; rewrite -label_single. }
    exact/hlocal_hempty. }
  { case=> [??]; rewrite /r'; case: ssrbool.ifP=> // [|?]. 
    { by move=> /= /lab_eqbP->; rewrite -label_single. }
    exact/hlocal_hempty. }
  { clear. move=> ? [][??]?; rewrite /gi /fi.
    (do ? case: classicT=> //)=>_->; do ? fequals; lia. }
  { clear. move=> ? [][??]?; rewrite /gi /fi.
    (do ? case: classicT=> //)=>_->; do ? fequals; lia. }
  { clear. move=> i; rewrite /fi /fsi'; clear.
    apply/fset_extens=> -[][] l1 l2 x.
    rewrite indom_fsubst; split; rewrite ?indom_label_eq.
    { case=> -[][]m1 m2 y; rewrite indom_label_eq.
      case: classicT=> [->|/[swap] ] [][]-><-->[][]-> //; split=> //.
      fequals; lia. }
    case=> -[]-><- ?.
    exists (Lab (l1, i) x); case: classicT=> //; rewrite indom_label_eq.
    (do ? split); do ? fequals; lia. }
  { rewrite /fsi' /f /fi; clear -iNj. move=> ? [][]l1 l2 x; rewrite indom_label_eq.
    rewrite indom_interval=> /[swap]; case=> -[]->->??.
    case: classicT=> // ?.
    case: classicT=> // [|[] ] // _.
    do ? fequals; lia. }
  { rewrite /f /fsi' /Fs; clear -N0 iNj=> -[][]l1 l2 x[][]m1 m2 y ?.
    do ? case:classicT=> //.
    { case=> ??->[]??->[]?. rewrite ?indom_Union.
      split; [exists l2|exists m2]; by rewrite indom_interval indom_label_eq. }
    all: try (move=> ???? []; lia).
    all: try (move=> ??? []?; by subst).
    move=> ???? [] *; have?: l2 = m2 by (lia). by subst. }
  { case=> -[]l1 l2 x; clear -iNj.
    split.
    { rewrite indom_fsubst=> -[][][]m1 m2 y[] /[swap].
      rewrite indom_union_eq=> -[].
      { rewrite indom_label_eq indom_single_eq=> -[][]<-<-<-.
        rewrite /f; case: classicT=> // ? []<-<-<-.
        rewrite /g; case: classicT=> // _.
        rewrite indom_union_eq indom_label_eq indom_single_eq; by left. }
      rewrite /Fs indom_Union /fsi' => -[k][]; rewrite indom_label_eq indom_interval=> I [][].
      move=> <- <- ind; rewrite /f; case: classicT=> //.
      case: classicT=> [|[] ] // _ _ []<-<-<-.
      rewrite indom_union_eq; right.
      rewrite /g; case: classicT=> //.
      case: classicT.
      { move=> _ _; rewrite indom_Union; exists (Get 0 N fsi1 y).
        rewrite indom_label_eq.
        by case: (Get_in _ I ind); do ? split. }
      case; split=> //; rewrite indom_Union; exists k.
      split=> //; by rewrite indom_interval. }
    rewrite indom_union_eq=> -[].
    { rewrite /g; (do ? case: classicT)=> [??|??|]; rewrite indom_label_eq.
      1,2: by move=> -[][]/iNj.
      move=> ? [][]<-<- ?.
      rewrite indom_fsubst; exists (⟨(i, 0), x⟩)%arr; split.
      { by rewrite /f; case: classicT. }
      by rewrite indom_union_eq; left; rewrite indom_label_eq. }
    rewrite /Fs indom_Union=> -[]k[]/[dup]?.
    rewrite indom_interval=> ?.
    rewrite /fsi'/ g; case: classicT=> [->|].
    {  case: classicT.
        { case=> -> ?; rewrite indom_label_eq=> -[][]??.
          rewrite indom_fsubst; exists (Lab (j, k) x); split.
          { rewrite /f; case: classicT=> // _.
            case: classicT=> // -[] //. }
          rewrite indom_union_eq indom_Union; right.
          exists k; by rewrite indom_label_eq. }
        move=> _; rewrite indom_label_eq=> -[][]. lia. }
      move=> ?; rewrite indom_label_eq=> -[][]. lia. }
    { case=> -[]l1 l2 x; clear -iNj.
      rewrite indom_union_eq=> -[]; rewrite indom_label_eq=> -[][]<-<-.
      { move=> ?; rewrite /f /g; do ? case: classicT=> //. }
      move=> /[dup] ?.
      rewrite indom_Union=> -[]k[]/[dup]?.
      rewrite indom_interval /g=> ??.
      case: classicT=> // _; case: classicT=> [|[]//] _.
      rewrite /f; case: classicT=> //=> _.
      case: classicT=> // -[].
      case: (@Get_in _ 0 N k x fsi1)=> //.
      rewrite indom_interval //. }
    { rewrite /f; clear -iNj.
      case=> -[]l1 l2 x. rewrite ?indom_label_eq indom_single_eq=> -[][]<-<-<-.
      by case: classicT. }
    { rewrite /gi; clear -iNj.
      case=> [][]l1 l2 x ?; rewrite indom_label_eq indom_single_eq.
      case=> -[]<-<- <-; case: classicT=> //. }
    { rewrite /fsi'=> ? _; clear -iNj.
      apply/disjoint_of_not_indom_both=> -[][]???.
      by rewrite ?indom_label_eq=> -[][]<- _ _ [][]/iNj. }
    { rewrite /fsi'=> ? _; clear -iNj.
      apply/disjoint_of_not_indom_both=> -[][]???.
      by rewrite ?indom_label_eq=> -[][]<- _ _ [][]/iNj. }
    { move=> ??; rewrite /fsi'; clear=> ?.
      apply/disjoint_of_not_indom_both=> -[][]???.
      rewrite ?indom_label_eq=> -[][]_ <-_[][]_ ?; by subst. }
    { move=> ?; rewrite -Union_label hstar_fset_Lab/= -H'E.
      rewrite /r' /= eqbxx; apply/PostH. }
    { move=> > ? hvP. apply/opP=> // * /=. apply/hvP.
      by rewrite indom_label_eq. }
    move=> l Q ?; move: (IH l Q).
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil.
    rewrite union_empty_r => {}IH.
    have->: 
      (fun hr : labeled D -> val => Inv (l + 1) \* (\*_(d <- ⟨(j, 0), fsi1 l⟩) r' d) \* Q \(m, vd) H' l ((hr \o f) \o set2 l)) = 
      (fun hr : labeled D -> val => Inv (l + 1) \* (\*_(d <- ⟨(j, 0), fsi1 l⟩) R' (el d)) \* Q \(m, vd) H' l hr).
    { apply/fun_ext_1=> ?; do 2? fequals.
      { by xsimpl; rewrite /r' /= eqbxx. }
      f_equal.
      apply/opP=> // x ? /=; case: classicT=> // _.
      case: classicT=> // -[]; split=> //; lia. }
    rewrite /r hstar_fset_Lab {1}/lab eqbxx -(hstar_fset_Lab (fun d => R(el d))).
    erewrite wp_ht_eq; first (apply/IH; lia).
    case=> l' ?; rewrite indom_union_eq ?indom_label_eq=> -[][??]; subst.
    { rewrite uni_in ?indom_label_eq //= /htrm_of.
      case: classicT=> //; autos*. }
    have?: (i, 0) <> (j, 0) by case.
    rewrite uni_nin ?indom_label_eq /= /htrm_of; autos*.
    do ? (case: classicT=> //=; autos* ).
    move=> [_]?[]; split=> //.
    rewrite indom_Union; setoid_rewrite indom_interval; do ? (eexists; eauto).
    all: lia.
Qed.

Hint Resolve eqbxx : lhtriple.