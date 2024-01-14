Set Implicit Arguments.
From LGTM.lib.theory Require Import LibListExt.
From LGTM.lib.seplog Require Import LibSepReference.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Import List.

Definition Sum_fma {A : Type} (s : binary64) (l : list A) (f : A -> binary64 * binary64) : binary64 := 
  fold_left (fun acc a => (@BFMA _ Tdouble (f a).1 (f a).2 acc)%F64) l s.

Definition dotprod_f64 {A : Type} := @Sum_fma A float_unit.

Lemma Sum_fma_filter0_feq {A : Type} (p : A -> bool) : forall (s : binary64) (l : list A) (f : A -> binary64 * binary64), 
  (forall a, In a l -> p a = false -> (f a).1 = float_unit \/ (f a).2 = float_unit) -> 
  (forall a, In a l -> @finite Tdouble (f a).1 /\ @finite Tdouble (f a).2) ->
  @feq Tdouble (Sum_fma s l f) (Sum_fma s (filter p l) f).
Proof.
  move=> s l. move: s.
  induction l as [ | a l IH ] using rev_ind; intros; auto.
  unfold Sum_fma in *. rewrite fold_left_app filter_app /=. 
  destruct (p a) eqn:Ef; rewrite ?IH //= ?fold_left_app //=.
  all: try (move=> a0 Hin; (apply H + apply H0); rewrite in_app_iff; tauto).
  specialize (H0 a). rewrite in_app_iff /= /finite in H0. 
  specialize (H0 (or_intror (or_introl eq_refl))). 
  apply H in Ef. 2: rewrite in_app_iff /=; tauto.
  destruct H0, Ef as [ -> | -> ]; rewrite ?BFMA_zero1 ?BFMA_zero2 //=.
Qed.

Lemma pair_fst_If {A B : Type} P (a b : A) (c : B) : 
  (If P then a else b, c) = If P then (a, c) else (b, c).
Proof. by case_if. Qed.

Lemma Sum_fma_eq {A : Type} (s : binary64) (l : list A) (f g : A -> binary64 * binary64) :
  (forall a, In a l -> f a = g a) -> Sum_fma s l f = Sum_fma s l g.
Proof.
  intros H. revert s. induction l; intros; simpl; auto. rewrite ?H ?IHl; simpl; auto.
  move=>*. rewrite H /=; tauto.
Qed.

Lemma Sum_fma_feq_base {A : Type} (s s' : binary64) (l : list A) (f : A -> binary64 * binary64) :
  @feq Tdouble s s' -> @feq Tdouble (Sum_fma s l f) (Sum_fma s' l f).
Proof. revert s s'. induction l; intros; simpl; auto. by apply IHl, BFMA_mor. Qed.

Lemma Sum_fma_feq {A : Type} (s : binary64) (l : list A) (f g : A -> binary64 * binary64) :
  (forall a, In a l -> @feq Tdouble (f a).1 (g a).1 /\ @feq Tdouble (f a).2 (g a).2) -> 
  @feq Tdouble (Sum_fma s l f) (Sum_fma s l g).
Proof.
  intros H. revert s. induction l; intros; simpl; auto. 
  pose proof (H a (or_introl eq_refl)) as (H1 & H2).
  etransitivity. 1: apply Sum_fma_feq_base, BFMA_mor; eauto.
  apply IHl=> a' Hin. apply H; simpl; auto.
Qed.

Corollary Sum_fma_filter_If {A : Type} (P : A -> Prop) (s : binary64) (l : list A) (f g : A -> binary64) 
  (Hfinf : forall a, In a l -> P a -> @finite Tdouble (f a))
  (Hfing : forall a, In a l -> @finite Tdouble (g a)) :
  @feq Tdouble (Sum_fma s l (fun i => If P i then (f i, g i) else (float_unit, g i))) 
    (Sum_fma s (filter (fun i => isTrue (P i)) l) (fun i => (f i, g i))).
Proof.
  rewrite -> Sum_fma_filter0_feq with (p:=fun i => isTrue (P i)).
  2:{ intros. rewrite -> isTrue_eq_false_eq in *. case_if; auto. }
  2:{ intros. case_if; simpl; auto. }
  rewrite -> Sum_fma_eq with (g:=fun i => (f i, g i)). 
  2:{ intros ? Hin%filter_In. rewrite isTrue_eq_true_eq in Hin. case_if; eqsolve. }
  reflexivity.
Qed.

Corollary Sum_fma_filter_If' {A : Type} (P : A -> Prop) (s : binary64) (l : list A) (f : A -> val) g
  (Hfinf : forall a, In a l -> P a -> @finite Tdouble (to_float (f a)))
  (Hfing : forall a, In a l -> @finite Tdouble ( (g a))) :
  @feq Tdouble (Sum_fma s l (fun i => (to_float (If P i then f i else float_unit), (g i)))) 
    (Sum_fma s (filter (fun i => isTrue (P i)) l) (fun i => (to_float (f i), g i))).
Proof.
  erewrite Sum_fma_eq; [ | move=> i0 ?; rewrite to_float_if pair_fst_If; reflexivity ].
  rewrite Sum_fma_filter_If -?sorted_bounded_sublist //.
Qed.

Lemma Sum_fma_list_interval (s : binary64) (l : list int) (f : int -> binary64 * binary64) 
  lb rb (H1 : 0 <= lb) (H2 : lb <= rb) (H3 : rb <= length l) :
  Sum_fma s (list_interval (abs lb) (abs rb) l) f = Sum_fma s (lof id (rb - lb)) (fun i => f (l[i + lb])).
Proof.
  unfold Sum_fma.
  match goal with 
    |- fold_left ?ff _ _ = _ => 
      pose proof (fold_left_map (lof id (rb - lb)) (fun a : int => l[a + lb]) ff s) as Htmp
  end.
  simpl in Htmp. rewrite Htmp. f_equal.
  assert (length (lof id (rb - lb)) = rb - lb :> int) as Hl1 by (rewrite length_lof; math).
  assert (length (list_interval (abs lb) (abs rb) l) = rb - lb :> int) as Hl2 by (rewrite list_interval_length; math).
  apply (nth_ext _ _ 0 0). 
  1: rewrite map_length; math.
  intros n Hlt. replace n with (abs n)%nat by math.
  rewrite (nth_map_lt 0) -?list_interval_nth ?nth_lof; try math. f_equal. math.
Qed.

Lemma Sum_fma_lof {A} (f : int -> A) s n (g : A -> _) : 
  Sum_fma s (projT1 (list_of_fun' f n)) g = 
  Sum_fma s (lof id n) (fun x => g (f x)).
Proof.
  unfold Sum_fma.
  match goal with 
    |- fold_left ?ff _ _ = _ => pose proof (fold_left_map (lof id n) f ff s) as Htmp
  end.
  simpl in Htmp. rewrite Htmp. f_equal. apply lof_indices'.
Qed.

(*
Lemma Sum_fma_filter_If {A : Type} (P : int -> Prop) (f g : A -> binary64 * binary64) : 
  forall (s : binary64) (l : list A) (f : A -> binary64 * binary64), 
  (forall a, In a l -> p a = false -> (f a).1 = float_unit \/ (f a).2 = float_unit) -> 
  (forall a, In a l -> @finite Tdouble (f a).1 /\ @finite Tdouble (f a).2) ->
  @feq Tdouble (Sum_fma s l f) (Sum_fma s (filter p l) f).
Proof.
*)

Fact finite_suffcond (l : list binary64) n (H : forall x, In x l -> @finite Tdouble x) :
  @finite Tdouble (nth n l float_unit).
Proof. destruct (nth_in_or_default n l float_unit) as [ | -> ]; auto. by compute. Qed.

Definition feq_val (v1 v2 : val) :=
  match v1, v2 with val_float f1, val_float f2 => @feq Tdouble f1 f2 | _, _ => v1 = v2 end.

Global Instance feq_val_eqrel : RelationClasses.Equivalence feq_val.
Proof.
  constructor; hnf. 1: intros []=> //=. 1: intros [] []=> /= ? //=; by symmetry.
  intros [] []=> //; intros [] => //. all: unfold feq_val; intros HH1; by rewrite HH1.
Qed.
