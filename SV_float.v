Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum Unary.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Struct2 Loops Loops2 Loops_float ListCommon.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

From Coq Require Import Permutation.

Open Scope Z_scope.

(* TODO maybe move this somewhere else *)
Module incr_float.

Section incr_float. 

Context {D : Type}.

Definition func :=
  (<{ fun "real_j" "x" =>
      let "tmp1" = ! "real_j" in
      let "tmp2" = "tmp1" .+ "x" in
      "real_j" := "tmp2" }>).

Lemma spec `{Inhab D} (pj0 : loc) (d : D) (j x : binary64) :
  htriple (single d tt)
  (fun=> func pj0 x) 
  (pj0 ~(d)~> val_float j)
    (fun=> pj0 ~(d)~> val_float (j + x)%F64).
Proof. by do 3 (xwp; xapp). Qed.

End incr_float.
End incr_float.

Notation "k '.+=' x" :=
  (incr_float.func k x)
  (in custom trm at level 58, format "k  .+=  x") : trm_scope.

Module fma.

Section fma. 

Context {D : Type}.

Definition func :=
  (<{ fun "z" "x" "y" =>
      let "tmp1" = "x" .* "y" in
      let "tmp2" = ! "z" in
      let "tmp2" = val_float_fma "tmp1" "tmp2" in
      "z" := "tmp2" }>).

Lemma spec `{Inhab D} (pj0 : loc) (d : D) (x y z : binary64) :
  htriple (single d tt)
  (fun=> func pj0 x y) 
  (pj0 ~(d)~> val_float z)
    (fun=> pj0 ~(d)~> val_float (@BFMA _ Tdouble x y z)).
Proof. by do 4 (xwp; xapp). Qed.

End fma.
End fma.

Coercion to_float : val >-> binary64.

Lemma to_float_if P a b : 
  to_float (If P then a else b) = If P then a else b.
Proof. by case: classicT. Qed.

Fact fold_left_map {A B C : Type} (l : list B) (g : B -> C) (f : A -> C -> A) (s : A) :
  List.fold_left (fun a b => f a (g b)) l s = List.fold_left f (List.map g l) s.
Proof.
  revert s. induction l as [ | x l IH ] using List.rev_ind; intros; rewrite ?List.map_app ?List.fold_left_app /= ?IH; auto. 
Qed. 

(*
(* This is not doable ... *)
Definition Sumf {A : Type} (l : list A) (f : A -> binary64) : binary64 := 
  List.fold_left (fun acc a => (acc + f a)%F64) l float_unit.

Lemma Sumf_filter {A : Type} (p : A -> bool) (l : list A) (f : A -> binary64) :
  (forall a, List.In a l -> p a = false -> f a = float_unit) -> 
  Sumf l f = Sumf (List.filter p l) f.
Proof.
  induction l as [ | a l IH ] using List.rev_ind; intros; auto.
  unfold Sumf in *. rewrite List.filter_app /=. destruct (p a); rewrite ?List.fold_left_app ?IH //=.
  /= IH.
Admitted.
*)

Definition Sum_fma {A : Type} (s : binary64) (l : list A) (f : A -> binary64 * binary64) : binary64 := 
  List.fold_left (fun acc a => (@BFMA _ Tdouble (f a).1 (f a).2 acc)%F64) l s.

Lemma Sum_fma_filter0_feq {A : Type} (p : A -> bool) : forall (s : binary64) (l : list A) (f : A -> binary64 * binary64), 
  (forall a, List.In a l -> p a = false -> (f a).1 = float_unit \/ (f a).2 = float_unit) -> 
  (forall a, List.In a l -> @finite Tdouble (f a).1 /\ @finite Tdouble (f a).2) ->
  @feq Tdouble (Sum_fma s l f) (Sum_fma s (List.filter p l) f).
Proof.
  move=> s l. move: s.
  induction l as [ | a l IH ] using List.rev_ind; intros; auto.
  unfold Sum_fma in *. rewrite List.fold_left_app List.filter_app /=. 
  destruct (p a) eqn:Ef; rewrite ?IH //= ?List.fold_left_app //=.
  all: try (move=> a0 Hin; (apply H + apply H0); rewrite List.in_app_iff; tauto).
  specialize (H0 a). rewrite List.in_app_iff /= /finite in H0. 
  specialize (H0 (or_intror (or_introl eq_refl))). 
  apply H in Ef. 2: rewrite List.in_app_iff /=; tauto.
  destruct H0, Ef as [ -> | -> ]; rewrite ?BFMA_zero1 ?BFMA_zero2 //=.
Qed.

Lemma pair_fst_If {A B : Type} P (a b : A) (c : B) : 
  (If P then a else b, c) = If P then (a, c) else (b, c).
Proof. by case_if. Qed.

Lemma Sum_fma_eq {A : Type} (s : binary64) (l : list A) (f g : A -> binary64 * binary64) :
  (forall a, List.In a l -> f a = g a) -> Sum_fma s l f = Sum_fma s l g.
Proof.
  intros H. revert s. induction l; intros; simpl; auto. rewrite ?H ?IHl; simpl; auto.
  move=>*. rewrite H /=; tauto.
Qed.

Lemma Sum_fma_feq_base {A : Type} (s s' : binary64) (l : list A) (f : A -> binary64 * binary64) :
  @feq Tdouble s s' -> @feq Tdouble (Sum_fma s l f) (Sum_fma s' l f).
Proof. revert s s'. induction l; intros; simpl; auto. by apply IHl, BFMA_mor. Qed.

Lemma Sum_fma_feq {A : Type} (s : binary64) (l : list A) (f g : A -> binary64 * binary64) :
  (forall a, List.In a l -> @feq Tdouble (f a).1 (g a).1 /\ @feq Tdouble (f a).2 (g a).2) -> 
  @feq Tdouble (Sum_fma s l f) (Sum_fma s l g).
Proof.
  intros H. revert s. induction l; intros; simpl; auto. 
  pose proof (H a (or_introl eq_refl)) as (H1 & H2).
  etransitivity. 1: apply Sum_fma_feq_base, BFMA_mor; eauto.
  apply IHl=> a' Hin. apply H; simpl; auto.
Qed.

Corollary Sum_fma_filter_If {A : Type} (P : A -> Prop) (s : binary64) (l : list A) (f g : A -> binary64) 
  (Hfinf : forall a, List.In a l -> P a -> @finite Tdouble (f a))
  (Hfing : forall a, List.In a l -> @finite Tdouble (g a)) :
  @feq Tdouble (Sum_fma s l (fun i => If P i then (f i, g i) else (float_unit, g i))) 
    (Sum_fma s (List.filter (fun i => isTrue (P i)) l) (fun i => (f i, g i))).
Proof.
  rewrite -> Sum_fma_filter0_feq with (p:=fun i => isTrue (P i)).
  2:{ intros. rewrite -> isTrue_eq_false_eq in *. case_if; auto. }
  2:{ intros. case_if; simpl; auto. }
  rewrite -> Sum_fma_eq with (g:=fun i => (f i, g i)). 
  2:{ intros ? Hin%List.filter_In. rewrite isTrue_eq_true_eq in Hin. case_if; eqsolve. }
  reflexivity.
Qed.

Corollary Sum_fma_filter_If' {A : Type} (P : A -> Prop) (s : binary64) (l : list A) (f : A -> val) g
  (Hfinf : forall a, List.In a l -> P a -> @finite Tdouble (to_float (f a)))
  (Hfing : forall a, List.In a l -> @finite Tdouble ( (g a))) :
  @feq Tdouble (Sum_fma s l (fun i => (to_float (If P i then f i else float_unit), (g i)))) 
    (Sum_fma s (List.filter (fun i => isTrue (P i)) l) (fun i => (to_float (f i), g i))).
Proof.
  erewrite Sum_fma_eq; [ | move=> i0 ?; rewrite to_float_if pair_fst_If; reflexivity ].
  rewrite Sum_fma_filter_If -?sorted_bounded_sublist //.
Qed.

Lemma Sum_fma_list_interval (s : binary64) (l : list int) (f : int -> binary64 * binary64) 
  lb rb (H1 : 0 <= lb) (H2 : lb <= rb) (H3 : rb <= List.length l) :
  Sum_fma s (list_interval (abs lb) (abs rb) l) f = Sum_fma s (lof id (rb - lb)) (fun i => f (l[i + lb])).
Proof.
  unfold Sum_fma.
  match goal with 
    |- List.fold_left ?ff _ _ = _ => 
      pose proof (fold_left_map (lof id (rb - lb)) (fun a : int => l[a + lb]) ff s) as Htmp
  end.
  simpl in Htmp. rewrite Htmp. f_equal.
  assert (List.length (lof id (rb - lb)) = rb - lb :> int) as Hl1 by (rewrite length_lof; math).
  assert (List.length (list_interval (abs lb) (abs rb) l) = rb - lb :> int) as Hl2 by (rewrite list_interval_length; math).
  apply (List.nth_ext _ _ 0 0). 
  1: rewrite List.map_length; math.
  intros n Hlt. replace n with (abs n)%nat by math.
  rewrite (nth_map_lt 0) -?list_interval_nth ?nth_lof; try math. f_equal. math.
Qed.

Lemma Sum_fma_lof {A} (f : int -> A) s n (g : A -> _) : 
  Sum_fma s (projT1 (list_of_fun' f n)) g = 
  Sum_fma s (lof id n) (fun x => g (f x)).
Proof.
  unfold Sum_fma.
  match goal with 
    |- List.fold_left ?ff _ _ = _ => pose proof (fold_left_map (lof id n) f ff s) as Htmp
  end.
  simpl in Htmp. rewrite Htmp. f_equal. apply lof_indices'.
Qed.

(*
Lemma Sum_fma_filter_If {A : Type} (P : int -> Prop) (f g : A -> binary64 * binary64) : 
  forall (s : binary64) (l : list A) (f : A -> binary64 * binary64), 
  (forall a, List.In a l -> p a = false -> (f a).1 = float_unit \/ (f a).2 = float_unit) -> 
  (forall a, List.In a l -> @finite Tdouble (f a).1 /\ @finite Tdouble (f a).2) ->
  @feq Tdouble (Sum_fma s l f) (Sum_fma s (List.filter p l) f).
Proof.
*)

Fact finite_suffcond (l : list binary64) n (H : forall x, List.In x l -> @finite Tdouble x) :
  @finite Tdouble (List.nth n l float_unit).
Proof. destruct (List.nth_in_or_default n l float_unit) as [ | -> ]; auto. by compute. Qed.

Module sv_float.

Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.

Section sv.

Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
(* sometimes Coq cannot tell whether lb is a variable or an int, so avoid using the same name lb here *)
Notation "'xlb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'xrb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.

Import List Vars.

Context (xind : list int).
Context (xval : list binary64).
Context (N M : int).
Context (lb rb : int).
Hypothesis (len : rb - lb = N).
Hypotheses (bounds_l: 0 <= lb) (bounds_r: lb <= rb).
Hypothesis len_xind : rb <= length xind.
Hypothesis len_xval : rb <= length xval.
Hypothesis nodup_xind : NoDup (list_interval (abs lb) (abs rb) xind).
Hypothesis sorted_xind : sorted (list_interval (abs lb) (abs rb) xind). (* TODO possibly remove nodup_xind since sorted_xind subsumes it? *)
Hypothesis xind_leq : forall x, In x (list_interval (abs lb) (abs rb) xind) -> 0 <= x < M.
Hypothesis xval_finite : forall x, In x (list_interval (abs lb) (abs rb) xval) -> @finite Tdouble x.

Tactic Notation "seclocal_solver" :=
  first [ rewrite list_interval_nth'; auto; math
    | rewrite list_interval_length; auto; math
    | rewrite -list_interval_nth; auto; math
    | idtac ]; auto.

Definition indexf := index_bounded.func.

Definition get := 
  <{
  fun i xind xval xlb xrb =>
    let k = indexf xlb xrb i xind in 
    let "k < rb" = k < xrb in
    if "k < rb" then
      xval[.k]
    else float_unit
}>.

Lemma get_spec {D} `{Inhab D} (x_ind x_val : loc) d (l : int): 
  @htriple D (single d tt) 
    (fun=> get l x_ind x_val lb rb)
    (harray_int xind x_ind d \* 
      harray_float xval x_val d)
    (fun hr => 
      harray_int xind x_ind d \* 
      harray_float xval x_val d).
Proof.
  xwp; xapp @index_bounded.spec=> //.
  xwp; xapp; xwp; xif=> ?; [xapp|xwp;xval]; xsimpl.
Qed.

Lemma get_spec_in {D : Type} `{Inhab D} (x_ind x_val : loc) i d : 
  @htriple D (single d tt) 
    (fun=> get (List.nth (abs i) (list_interval (abs lb) (abs rb) xind) 0) x_ind x_val lb rb)
    (\[0 <= i < N] \*
      harray_int xind x_ind d \* 
      harray_float xval x_val d)
    (fun hr => 
     \[hr = fun=> List.nth (abs i) (list_interval (abs lb) (abs rb) xval) float_unit] \* 
      harray_int xind x_ind d \* 
      harray_float xval x_val d).
Proof with seclocal_solver.
  rewrite -wp_equiv; xsimpl=> ?.
  xwp; xapp (@index_bounded.spec _ H)=> //.
  xwp; xapp. rewrite index_nodup; auto...
  xwp; xif=> ?; subst; try math.
  xapp; xsimpl*...
Qed.

Lemma get_spec_out_unary {D : Type} `{Inhab D} (x_ind x_val : loc) (i : int) d : 
  @htriple D (single d tt) 
    (fun=> get i x_ind x_val lb rb)
    (\[~ In i (list_interval (abs lb) (abs rb) xind)] \*
      harray_int xind x_ind d \* 
      harray_float xval x_val d)
    (fun hr => 
     \[hr = fun=> float_unit] \* 
      harray_int xind x_ind d \* 
      harray_float xval x_val d).
Proof.
  rewrite -wp_equiv; xsimpl=> ?.
  xwp; xapp (@index_bounded.spec _ H)=> //...
  rewrite memNindex // list_interval_length //.
  xwp; xapp. xwp; xif=> ?; try math. xwp; xval. xsimpl*.
Qed.

Local Notation D := (labeled int).

Lemma get_spec_out `{Inhab D} fs (x_ind x_val : loc) : 
  @htriple D fs
    (fun i => get (eld i) x_ind x_val lb rb)
    (\[forall d, indom fs d -> ~ In (eld d) (list_interval (abs lb) (abs rb) xind)] \*
      (\*_(d <- fs) harray_int xind x_ind d) \* 
       \*_(d <- fs) harray_float xval x_val d)
    (fun hr => 
     \[hr = fun=> float_unit] \* 
      ((\*_(d <- fs) harray_int xind x_ind d) \* 
       \*_(d <- fs) harray_float xval x_val d)).
Proof.
  apply/htriple_val_eq/htriple_conseq;
  [|eauto|move=> ?]; rewrite -hstar_fset_pure -?hbig_fset_hstar; first last.
  { move=> ?; apply: applys_eq_init; reflexivity. }
  apply/htriple_union_pointwise=> [> -> //|??]. 
  rewrite -wp_equiv wp_single; xapp (@get_spec_out_unary D)=> // ??->.
  xsimpl*.
Qed.

Definition sum := 
  <{
  fun xind xval xlb xrb =>
  let s = ref float_unit in
  for i <- [xlb, xrb] {
    let x = xval[.i] in 
    (* s += x *)
    s .+= x
  };
  let "res" = ! s in
  free s;
  "res"
}>.

(* Tactic Notation "xin" constr(S1) ":" tactic(tac) := 
  let n := constr:(S1) in
  xfocus n; tac; try(
  first [xunfocus | xcleanup n]; simpl; try apply xnwp0_lemma). *)
Lemma val_float_eq i j : 
  (val_float i = val_float j) = (i = j).
Proof. by extens; split=> [[]|]->. Qed.

Ltac fold' := 
  rewrite ?label_single ?wp_single ?val_float_eq
    (* -/(incr _)  *)
    -/float_unit
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

(*
Fact Sum_interval_change2 (f : int -> int) (a b : int) :
  Sum (interval 0 (b - a)) f = Sum (interval a b) (fun i => f (i - a)).
Proof.
  rewrite -> Sum_interval_change with (c := a).
  do ? f_equal; lia.
Qed.

Fact Sum1 {A : Type} (s : A) (f : A -> int) : 
  Sum (`{s}) f = f s.
Proof.
  rewrite update_empty SumUpdate; [ rewrite Sum0 Z.add_0_l; reflexivity | auto ].
Qed.
*)

Notation "l '[[' i '--' j ']]' " := (list_interval (abs i) (abs j) l) (at level 5).

(*
Lemma sum_spec `{Inhab D} (x_ind x_val : loc) : 
  {{ arr(x_ind, xind)⟨1, 0⟩ \*
     .arr(x_val, xval)⟨1, 0⟩ \\* 
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) .arr(x_val, xval)⟨2, i⟩) }}
  [{
    [1| ld in `{0}         => sum x_ind x_val lb rb];
    {2| ld in `[0, M]          => get ld x_ind x_val lb rb}
  }]
  {{ hv, (\exists perm : list int, 
    \[Permutation (lof id M) perm /\ 
    (* stating that xind is a subsequence of perm may be beneficial, but is it needed? *)
    (* this is exact, no feq is needed *)
    (feq (hv[`1](0)) (Sumf (lof int M) (to_float \o (fun i => hv[`2](i)))))  \* 
      arr(x_ind, xind)⟨1, 0⟩ \*
      .arr(x_val, xval)⟨1, 0⟩ \* 
      (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
      (\*_(i <- `[0, M]) .arr(x_val, xval)⟨2, i⟩)}}.
Proof with fold'.
  xfocus (2,0) xind[[lb -- rb]].
  rewrite (hbig_fset_part (`[0, M]) xind[[lb -- rb]]). (* TODO: move to xfocus *)
  xapp get_spec_out=> //.
  { case=> ?? /[! @indom_label_eq]-[_]/=; rewrite /intr filter_indom; autos*. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); set (H2 := hbig_fset hstar (_ ∖ _) _).
  xframe2 H1. xframe2 H2. xsimpl.
  xin (1,0) : xwp; xapp=> q...
  have Hl : length xind[[lb -- rb]] = rb - lb :> int.
  1: rewrite -> list_interval_length; try math.
  rewrite intr_list ?(fset_of_list_nodup 0) ?Hl ?Union_interval_change2 //.
  set (R (i : int) := arr(x_ind, xind)⟨2, i⟩ \* .arr(x_val, xval)⟨2, i⟩).
  set (Inv (i : int) := arr(x_ind, xind)⟨1, 0⟩ \* .arr(x_val, xval)⟨1, 0⟩).
  xfor_sum_float Inv R R (fun hv i => hv[`2](xind[i])) q.
  { rewrite /Inv /R.
    (xin (1,0): (xwp; xapp; xapp (@incr_float.spec  _ H)=> y))...
    xapp (@get_spec_in D)=> //; try math. xsimpl*.
    rewrite <- list_interval_nth with (l:=xval); try math.
    replace (lb + (l0 - lb)) with l0 by math. xsimpl*. }
  { intros Hneq Hi Hj Hq. apply Hneq. 
    enough (abs (i0 - lb) = abs (j0 - lb) :> nat) by math.
    eapply NoDup_nth. 4: apply Hq. all: try math; try assumption. }  
  { rewrite -list_interval_nth; try f_equal; lia. }
  xwp; xapp... xwp; xapp. xwp; xval. 
  case (classicT (0 <= M))=> C.
  2: admit.
  (* long and hard, but still possible to be extracted and solved *)
  pose proof (nodup_bounded_makeperm_bypre C nodup_xind xind_leq) as (l' & Hnodup & Hbounded & Hlen).
  xsimpl* (List.app l' (xind [[lb -- rb]])). 
  split. 1: by apply nodup_bounded_saturate.
  pose proof (nodup_bounded_length_le C nodup_xind xind_leq) as Hle.
  rewrite list_interval_length in Hle...
  destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
  destruct (list_of_fun' _ _) as (l2 & Hlen2 & Hl2); simpl.
  assert (l2 = (repeat float_unit (abs (M - N))) ++ l1) as ->.
  { apply List.nth_ext with (d:=float_unit) (d':=float_unit).
    1: rewrite List.app_length repeat_length; math.
    intros i0 Hi0. replace i0 with (abs i0) by math.
    rewrite -> Hl2; try math. case_if.
    { rewrite /Sum.mem in C0.
      admit. } 
    { admit. } }
  rewrite fold_left_app fold_left_BPLUS_unit //.
Abort.
*)

Context (dvec : list binary64).
Context (dvec_len : length dvec = M :> int).
Hypothesis dvec_finite : forall x, In x dvec -> @finite Tdouble x.

Definition dotprod := 
  <{
  fun xind xval dvec xlb xrb =>
  let s = ref float_unit in
  for i <- [xlb, xrb] {
    let x = xval[.i] in 
    let i = xind[i] in 
    let v = dvec[.i] in 
    fma.func s x v
  };
  let "res" = ! s in
  free s;
  "res"
}>.

Lemma dotprod_spec `{Inhab D} (x_ind x_val d_vec : loc) : 
  {{ arr(x_ind, xind)⟨1, 0⟩ \\*
     .arr(x_val, xval)⟨1, 0⟩ \\*
     .arr(d_vec, dvec)⟨1, 0⟩ \\* 
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) .arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, M]) .arr(d_vec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{0}   => dotprod x_ind x_val d_vec lb rb];
    [2| ld in `[0,M] => get ld x_ind x_val lb rb]
  }]
  {{ hv, (* \exists ans : binary64, *) (* xnapp cannot handle this *)
    \[feq_val (hv[`1](0))
      (val_float (Sum_fma float_unit (lof id M) (fun i => (to_float (hv[`2](i)), dvec[i]))))] \* 
     arr(x_ind, xind)⟨1, 0⟩ \\*
     .arr(x_val, xval)⟨1, 0⟩ \\*
     .arr(d_vec, dvec)⟨1, 0⟩ \\* 
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) .arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, M]) .arr(d_vec, dvec)⟨2, i⟩)}}.
Proof with (try solve [ seclocal_solver | auto using finite_suffcond ]; fold').
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus* (2,0) xind[[lb -- rb]].
  xapp get_spec_out=> //. 1: case=> ??; indomE; autos*.
  xclean_heap.
  xin (1,0) : xwp; xapp=> q...
  have Hl : length xind[[lb -- rb]] = rb - lb :> int by apply list_interval_length.
  rewrite intr_list ?(fset_of_list_nodup 0) ?Hl ?Union_interval_change2 //.
  xfor_sum_fma Inv R R (fun hv i => (to_float (hv[`2](xind[i])), dvec[xind[i] ])) q...
  { (xin (1,0): do 3 (xwp; xapp); xapp (@fma.spec _ H)=> y)...
    xapp (@get_spec_in D)=> //; try math. xsimpl*... auto using finite_suffcond. }
  { move=>Ha Hb Hc; have Ha' : i0 - lb <> j0 - lb by math.
    move: Ha'; apply contrapose, NoDup_nthZ; autos*; math. }
  intros Hfin. simpl in Hfin. xwp; xapp... xwp; xapp. xwp; xval. xsimpl*. simpl.
  rewrite Sum_fma_filter_If' -?sorted_bounded_sublist //...
  2:{ intros a0 _ (n & Hn & <-)%(In_nth _ _ 0). replace n with (abs n) by math.
    rewrite -list_interval_nth; try math. apply Hfin; math. }
  rewrite -/(Sum_fma _ _ _) (Sum_fma_lof) /= Sum_fma_list_interval //=.
Qed.

End sv. 
(*
Section sv.

Import List.

Definition slice {A} (l : list A) i j := (list_interval (abs i) (abs j) l).

Context (xind xval yind yval : list int).
Context (Nx Ny M rbx lbx rby lby : int).
(* Hypothesis lenx : rbx - lbx = Nx. *)
(* Hypothesis leny : rby - lby = Nx. *)
Hypothesis (bounds_lx : 0 <= lbx) (bound_rx : lbx <= rbx).
Hypothesis (bounds_ly : 0 <= lby) (bound_ry : lby <= rby).
Hypothesis len_xind : rbx <= length xind.
Hypothesis len_xval : rbx <= length xval.
Hypothesis len_yind : rby <= length yind.
Hypothesis len_yval : rby <= length yval.
Hypothesis sorted_xind : sorted (slice xind lbx rbx).
Hypothesis sorted_yind : sorted (slice yind lby rby).
Hypothesis xind_leq : forall x, In x (slice xind lbx rbx) -> 0 <= x < M.
Hypothesis yind_leq : forall x, In x (slice yind lby rby) -> 0 <= x < M.


(* Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope. *)
(* Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope. *)
(* Notation "'yind'" := ("y_ind":var) (in custom trm at level 0) : trm_scope. *)
(* Notation "'yval'" := ("y_val":var) (in custom trm at level 0) : trm_scope. *)
Notation "'rbx'" := ("rb_x":var) (in custom trm at level 0) : trm_scope.
Notation "'lbx'" := ("lb_x":var) (in custom trm at level 0) : trm_scope.
Notation "'rby'" := ("rb_y":var) (in custom trm at level 0) : trm_scope.
Notation "'lby'" := ("lb_y":var) (in custom trm at level 0) : trm_scope.
Notation "'iX'" := ("iX":var) (in custom trm at level 0) : trm_scope.
Notation "'iY'" := ("iY":var) (in custom trm at level 0) : trm_scope.
Notation "'ans'" := ("ans":var) (in custom trm at level 0) : trm_scope.

Notation "'while' C '{' T '}'"  :=
  (While C T)
  (in custom trm at level 69,
    C, T at level 0,
    format "'[' while  C ']'  '{' '/   ' '[' T  '}' ']'") : trm_scope.

Definition sv_dotprod (xind yind xval yval : loc) := <{
  fun lbx rbx lby rby  =>
    let ans = ref 0 in
    let iX = ref lbx in 
    let iY = ref lby in 
      while (
        let "ix" = !iX in
        let "iy" = !iY in
        let "iXl" = "ix" < rbx in 
        let "iYl" = "iy" < rby in
        "iXl" && "iYl") {
        let "ix" = !iX in
        let "iy" = !iY in
        let "iXind" = xind["ix"] in 
        let "iYind" = yind["iy"] in 
        let "cnd" = "iXind" = "iYind" in 
        if "cnd" then 
          let "iXind" = xval["ix"] in 
          let "iYind" = yval["iy"] in 
          let "val" = "iXind" * "iYind" in
          ans += "val";
          ++iX;
          ++iY
        else 
          let "cnd" = "iXind" < "iYind" in 
          if "cnd" then 
            ++iX 
          else ++iY
      }; 
      let "s" = !ans in 
      free iX; free iY; free ans;
      "s"
}>.

Definition arr1 x_ind y_ind x_val y_val := 
  arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \*
  arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩.

Ltac fold' := 
  rewrite ?label_single ?wp_single ?val_int_eq
    -/(While_aux _ _) 
    -/(While _ _) //=; try lia.

Notation size := Datatypes.length.

Lemma not_isTrueE (P: Prop) : (~ isTrue P) = ~ P.
Proof.
Admitted.

Ltac bool_rew := 
  rewrite ?false_eq_isTrue_eq ?istrue_isTrue_eq 
    ?true_eq_isTrue_eq -?(isTrue_and, isTrue_not, isTrue_or) ?not_isTrueE.

Hint Resolve lhtriple_free : lhtriple.

Lemma sv_dotprod_spec `{Inhab (labeled int)} (x_ind x_val y_ind y_val : loc) : 
  {{ (arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \*
     arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩) \*
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, M]) arr(y_ind, yind)⟨3, i⟩) \\*
     (\*_(i <- `[0, M]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    {1| ld in `{0}   => sv_dotprod x_ind y_ind x_val y_val lbx rbx lby rby};
    {2| ld in `[0,M] => get ld x_ind x_val lbx rbx};
    {3| ld in `[0,M] => get ld y_ind y_val lby rby}
  }]
  {{ hv, \[hv[`1](0) = Σ_(i <- `[0,M]) (hv[`2](i) * hv[`3](i))] \* 
      (arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \*
      arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩) \*
      (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
      (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) \\* 
      (\*_(i <- `[0, M]) arr(y_ind, yind)⟨3, i⟩) \\*
      (\*_(i <- `[0, M]) arr(y_val, yval)⟨3, i⟩)}}.
Proof with fold'.
  set (sxind := (slice xind lbx rbx)).
  set (syind := (slice yind lby rby)).
  set (sxval := (slice xval lbx rbx)).
  set (syval := (slice yval lby rby)).
  set (ind := merge sxind syind).
  have?: NoDup sxind by exact/sorted_nodup.
  have?: NoDup syind by exact/sorted_nodup.
  rewrite -/(arr1 _ _ _ _).
  have ndind: NoDup ind by exact/sorted_nodup/sorted_merge.
  xfocus (2,0) (ind).
  rewrite {1 2 5 6}(hbig_fset_part `[0, M] ind).
  xapp (@get_spec_out xind xval); eauto.
  { case=> ??/=/[!@indom_label_eq]-[_].
    rewrite /intr filter_indom/= /Sum.mem/ind In_merge; autos*. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); 
  set (H2 := hbig_fset hstar (_ ∖ _) _).
  xframe2 H1; xframe2 H2; xsimpl; clear H1 H2.
  xfocus (3,0) ind.
  rewrite (hbig_fset_part `[0, M] ind).
  xapp (@get_spec_out yind yval); eauto.
  { case=> ??/=/[!@indom_label_eq]-[_].
    rewrite /intr filter_indom/= /Sum.mem/ind In_merge; autos*. }
  set (H1 := hbig_fset hstar (_ ∖ _) _); 
  set (H2 := hbig_fset hstar (_ ∖ _) _).
  xframe2 H1; xframe2 H2; xsimpl; clear H1 H2.
  set (H1 := _ \* hbig_fset _ _ _); set (H2 := _ \* H1); set (arrs := _ \* H2).
  xin (1,0) : xwp; xapp=> ans; xwp; xapp=> iX; xwp; xapp=> iY...
  have Hlx : length sxind = rbx - lbx :> int.
  1: rewrite /sxind list_interval_length; try math.
  have Hly : length syind = rby - lby :> int.
  1: rewrite /syind list_interval_length; try math.
  have E : `[0,M] ∩ ind = ind.
  { apply/fset_extens=> ?. 
    rewrite /intr filter_indom /ind -fset_of_list_in /Sum.mem ?In_merge; splits*.
    rewrite ?indom_interval=> -[]; autos*. }
  rewrite ?E (fset_of_list_nodup 0) //.
  set (cond ix iy := isTrue (ix < rbx /\ iy < rby)).
  set (Inv (b : bool) (i : int) := 
    arr1 x_ind y_ind x_val y_val \*
    \exists (ix iy : int), 
      iY ~⟨(1, 0)%Z, 0⟩~> iy \* iX ~⟨(1, 0)%Z, 0⟩~> ix \*
      \[(i = size ind -> ~ b) /\ lbx <= ix /\ lby <= iy /\
        (i < size ind -> ind[i] > max (take (abs (ix - lbx)) sxind)) /\
        (i < size ind -> ind[i] > max (take (abs (iy - lby)) syind)) /\ 
        b = cond ix iy /\
        (b -> 
          (ind[i] = Z.min xind[ix] yind[iy] /\ 
          (forall x, In x sxind -> x < xind[ix] -> x < yind[iy]) /\  
          (forall y, In y syind -> y < yind[iy] -> y < xind[ix])))]).
  set (op hv i := hv[`2](ind[i]) * hv[`3](ind[i])).
  set (R1 (i : int) := arr(y_ind, yind)⟨3,i⟩ \* arr(y_val, yval)⟨3,i⟩).
  set (R2 (i : int) := arr(x_ind, xind)⟨2,i⟩ \* arr(x_val, xval)⟨2,i⟩).
  have xindE : forall i, lbx <= i < rbx -> xind[i] = sxind[i-lbx].
  { move=> *; rewrite -list_interval_nth; try f_equal... }
  have yindE : forall i, lby <= i < rby -> yind[i] = syind[i-lby].
  { move=> *; rewrite -list_interval_nth; try f_equal... }
  have xvalE : forall i, lbx <= i < rbx -> xval[i] = sxval[i-lbx].
  { move=> *; rewrite -list_interval_nth; try f_equal... }
  have yvalE : forall i, lby <= i < rby -> yval[i] = syval[i-lby].
  { move=> *; rewrite -list_interval_nth; try f_equal... }
  have sE : forall a b, a - b + 1 = a + 1 - b by lia.
  xwhile_sum Inv R1 R2 R1 R2 op ans=> //.
  { move=> l s ?.
    rewrite {1}/Inv; xnsimpl=> ix iy[?][?][?][LM1][LM2][].
    rewrite /cond. bool_rew=> -[??]/(_ eq_refl)-[]indlE[L1 L2].
    rewrite /arr1; clear arrs H1 H2.
    xin (1,0): do 5 (xwp; xapp); xwp; xif=> C.
    { xin (1,0): 
        do 3 (xwp; xapp); xwp; xapp @incr.spec; 
        (xwp; xapp @incr1.spec); xapp @incr1.spec=> ?.
      rewrite /op /=; rewrite <-?hstar_assoc.
      set (Heap := _ \* harray_int xind _ _); rewrite /R2...
      rewrite val_int_eq in C; rewrite {-1 4 6}indlE -C Z.min_id xindE...
      xin (2,0): fold'; xapp get_spec_in; eauto...
      rewrite /R1 indlE C Z.min_id yindE...
      xapp get_spec_in; eauto...
      rewrite /Heap /Inv /arr1/cond.
      have SlE: 
        l + 1 = size ind -> 
          ~ (ix - lbx + 1 < rbx - lbx /\ iy - lby + 1 < rby - lby). 
      { move: C indlE=>-> /[! Z.min_id]/[swap]/sorted_max_size->; bool_rew.
        have: max ind >= max syind by apply/max_sublist=>?; rewrite In_merge; right.
        rewrite yindE...
        move=>/[swap]->/nth_le_max-> //; lia. }
      rewrite -xvalE -?yvalE...
      xsimpl (ix + 1) (iy + 1); splits; [|lia|lia| | |autos*|]...
      { bool_rew... }
      { move=> ?; rewrite -sE max_takeS -?xindE... 
        suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      { replace (iy + 1 - lby) with (iy - lby + 1) by lia.
        move=> ?; rewrite max_takeS -?yindE...
        suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      bool_rew=> -[]??; splits*.
      { rewrite merge_nthS // -/ind; try lia.
        rewrite indlE {2}C -{1}C ?Z.min_id xindE ?yindE ?search_nth...
        rewrite xindE ?yindE; first do 2 f_equal... }
      { move=> x ??; move: (@sorted_le (iy -lby) (iy +1 - lby) syind sorted_yind).
        rewrite -?yindE...
        suff: (x <= xind[ix]) by lia.
        rewrite xindE; first apply/In_lt; rewrite ?sE -?xindE... }
      move=> y ??; move: (@sorted_le (ix -lbx) (ix +1 - lbx) sxind sorted_xind).
      rewrite -?xindE...
      suff: (y <= yind[iy]) by lia.
      rewrite yindE; first apply/In_lt; rewrite ?sE -?yindE... }
    rewrite /op.
    xin (1,0): xwp; xapp; xwp; xif=> L; xapp @incr1.spec=> ?.
    { rewrite /op /=; rewrite <-?hstar_assoc.
      set (Heap := _ \* harray_int yval _ _); rewrite /R2...
      rewrite indlE Z.min_l... rewrite (xindE ix)...
      xin (2,0): fold'; xapp get_spec_in; eauto...
      rewrite /R1; xapp get_spec_out_unary; eauto.
      { move/L2; rewrite -xindE... }
      rewrite Z.mul_0_r Z.add_0_r.
      rewrite /Heap /Inv /arr1/cond.
      have SlE: 
        l + 1 = size ind -> 
          ~ (ix - lbx + 1 < rbx - lbx /\ iy - lby < rby - lby). 
      { move: indlE=> /[!Z.min_l] //; last lia. 
        move=>/[swap]/sorted_max_size->; bool_rew.
        have: max ind >= max sxind by apply/max_sublist=>?; rewrite In_merge; left.
        move=>/[swap]->; rewrite xindE... move/nth_le_max->... }
      xsimpl (ix + 1) (iy); splits; [|lia|lia| | |autos*|].
      { bool_rew... }
      { move=> ?; rewrite -sE max_takeS -?xindE...
        suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      { move=> ?. suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      bool_rew=> -[]??; splits*.
      { rewrite merge_nthS -/ind ?indlE 1?(Z.min_l (_[_]))...
        rewrite xindE ?search_nth ?sE -?xindE ?yindE...
        erewrite search_lt_nth; eauto...
        all: rewrite -yindE...
        move=> ? /L2; lia. }
      { move=> x ??; move: (@sorted_le (ix -lbx) (ix +1 - lbx) sxind sorted_xind).
        rewrite -?xindE...
        suff: (x <= xind[ix]) by lia.
        rewrite xindE; first apply/In_lt; rewrite ?sE -?xindE... }
      move=> ? /L2/[apply]; rewrite ?xindE...
      move:  (@sorted_le (ix -lbx) (ix +1 - lbx) sxind sorted_xind)... }
    rewrite /op /=; rewrite <-?hstar_assoc.
    set (Heap := _ \* harray_int yval _ _); rewrite /R1...
    rewrite indlE Z.min_r... rewrite (yindE iy)...
    xin (3,0): fold'; xapp get_spec_in...
    rewrite /R2; xapp get_spec_out_unary; eauto.
    { move/L1. rewrite val_int_eq in C; rewrite -yindE... }
    rewrite Z.mul_0_l Z.add_0_r.
    have SlE: 
    l + 1 = size ind -> 
      ~ (ix - lbx < rbx - lbx /\ iy - lby + 1 < rby - lby). 
    { move: indlE=> /[!Z.min_r] //; last lia. 
      move=>/[swap]/sorted_max_size->; bool_rew.
      have: max ind >= max syind by apply/max_sublist=>?; rewrite In_merge; right.
      move=>/[swap]->; rewrite yindE... move/nth_le_max->... }
    rewrite val_int_eq in C.
    rewrite /Heap /Inv /arr1/cond; xsimpl (ix) (iy+1); splits; [|lia|lia| | |autos*|].
    { bool_rew... }
    { move=> ?. suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia.
      exact/sorted_merge. }
    { move=> ?; rewrite -sE max_takeS -?yindE...
      suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia.
      exact/sorted_merge. }
    bool_rew=> -[]??; splits*.
    { rewrite merge_nthS -/ind ?indlE 1?(Z.min_r (_[_]))...
      rewrite yindE ?search_nth ?sE -?yindE ?xindE...
      erewrite search_lt_nth; eauto...
      all: rewrite -xindE...
      move=> ? /L1; lia. }
    { move=> ? /L1/[apply]; rewrite ?yindE...
      move: (@sorted_le (iy - lby) (iy+1-lby) syind sorted_yind); lia. }
    move=> y ??; move: (@sorted_le (iy -lby) (iy +1 - lby) syind sorted_yind).
    rewrite -yindE...
    suff: (y <= yind[iy]) by lia.
    rewrite yindE; first apply/In_lt; rewrite ?sE -?yindE... }
  { move=> l *; rewrite /Inv/op/ntriple.
    xpull=> ix iy []_[]?[]?[]L1[]L2; rewrite /cond; bool_rew=> /[!not_and_eq]-[] []G _.
    { rewrite /R1.
      xin (3,0): fold'; xapp get_spec=> *...
      rewrite /R2.
      xapp get_spec_out_unary...
      { move/max_le; move: L1; rewrite take_ge ?length_List_length; try math.
        rewrite -/(slice _ _ _)-/sxind; lia. }
      xsimpl; try math.
      splits*=> //.
      { move=> ?. suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
      { move=> ?. suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia.
        exact/sorted_merge. }
        bool_rew; lia. }
    rewrite /R2.
    xin (2,0): fold'; xapp get_spec=> *...
    rewrite /R1.
    xapp get_spec_out_unary...
    { move/max_le; move: L2; rewrite take_ge ?length_List_length; try math.
      rewrite -/(slice _ _ _)-/syind; lia. }
    xsimpl; try lia.
    splits*=> //.
    { move=> ?. suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia.
      exact/sorted_merge. }
    { move=> ?. suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia.
      exact/sorted_merge. }
    bool_rew; lia. }
  { move=> ???. rewrite /ntriple -xnwp1_lemma /=.
    rewrite /Inv; xpull=> ix iy C.
    do ? (xwp; xapp). xapp @and.spec=> //.
    move=> ? E'; bool_rew; case: (C)=> ? [?][?][?][?][] ?.
    xsimpl=> // ?; subst; rewrite E' /cond. by bool_rew.  }
  { move=> ?? []/(_ eq_refl); by case: b. }
  { move=> *. move/NoDup_nthZ: ndind=> /[apply]; lia. }
  { move=> *. move/NoDup_nthZ: ndind=> /[apply]; lia. }
  { rewrite /arr1 /Inv/arrs/arr1; xsimpl lbx lby.
    { splits; [|lia|lia| | |autos*|].
      { rewrite /cond/ind; bool_rew; move: (size_merge sxind syind); lia. }
        { rewrite Z.sub_diag abs_0 /= max0=> ?.
          have: (In (nth 0 ind 0) ind) by apply/nth_In; lia.
          rewrite In_merge=> -[/xind_leq|/yind_leq]; lia. }
        { rewrite Z.sub_diag abs_0 /= max0=> ?.
          have: (In (nth 0 ind 0) ind) by apply/nth_In; lia.
          rewrite In_merge=> -[/xind_leq|/yind_leq]; lia. }
        rewrite /cond; bool_rew; do ? split; rewrite ?xindE ?yindE ?Z.sub_diag...
        { rewrite merge_nth0... }
        { move=> ?/(In_le_0 _ _ sorted_xind); rewrite -/sxind; lia. }
        move=> ?/(In_le_0 _ _ sorted_yind); rewrite -/syind; lia. }
    rewrite /H2/H1 ?E (fset_of_list_nodup 0) // /R1 /R2.
    rewrite -> ?hbig_fset_hstar; xsimpl*. }
  simpl=> v; rewrite /op/R1/R2/Inv/arr1/arrs/H2/H1 E -fset_of_list_nodup //.
  rewrite -> ?hbig_fset_hstar; xsimpl=> ?? _. 
  do 4 (xwp; xapp); xwp; xval; xsimpl; rewrite /op.
  rewrite (@SumEq _ _
    (fun i => If ind i then v[`2](i) *  v[`3](i) else 0) 
    `[0, M]).
  { rewrite (SumIf (fun=> id)) E (SumList 0) // Sum0s; f_equal; math. }
  by move=> ?; case: classicT.
Qed.

End sv.
*)
End sv_float.