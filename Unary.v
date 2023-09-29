Set Implicit Arguments.
From SLF Require Import Fun LabType.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct Loops.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

(* Module NatDom : Domain with Definition type := nat.
Definition type := nat.
End NatDom.

Module IntDom : Domain with Definition type := int.
Definition type := int.
End IntDom.

Module Export AD := WithArray(IntDom).
Check eq_refl : D = labeled int.

Global Instance Inhab_D : Inhab D. 
Proof Build_Inhab (ex_intro (fun=> True) (Lab (0, 0) 0) I). *)

(*
  cooi i x_ind x_val = 
    k = 0
    while (i != x_ind[k] && i < lenght x_ind)
      k++
*)


Section pure_facts.

Implicit Type l s : list int.
Implicit Type i : int.

Export List.

Definition index i l : int. Admitted.
Lemma index_nodup i l : 
  0 <= i < length l ->
  List.NoDup l -> 
    index (nth (abs i) l 0) l = i.
Proof.
Admitted.

Lemma in_take x l i : 0 <= i <= length l -> (In x (take (abs i) l)) = (index x l < i).
Proof.
Admitted.

Lemma nth_index x s : In x s -> nth (abs (index x s)) s 0 = x.
Admitted.

Lemma index_mem x s : (index x s < length s) = (In x s).
Admitted.

Lemma index_size x s : index x s <= length s.
Proof. Admitted.

Lemma indexG0 x s : 0 <= index x s.
Proof. Admitted.

Lemma memNindex x s :  ~In x s -> index x s = length s.
Admitted.


End pure_facts.

Module and.

Definition func :=
  <{fun 'b 'c =>
    if 'b then 'c 
    else false
  }>.

Lemma spec (b c : bool) d : 
  htriple (single d tt) 
    (fun=> func b c)
    \[]
    (fun hr => \[hr d = b && c]).
Proof.
  xwp; xif=> bp; xwp; xval; xsimpl.
  all: by case: c b bp=> -[].
Qed.

End and.

Notation "t1 && t2" :=
  (and.func t1 t2)
  (in custom trm at level 58) : trm_scope.

Hint Resolve and.spec : htriple.

Module incr1.

Definition func :=
  (<{ fun "real_j" =>
      let "tmp1" = ! "real_j" in
      let "tmp2" = "tmp1" + 1 in
      "real_j" := "tmp2" }>).

Lemma spec (pj0 : loc) (d : D) (j : int) :
  htriple (single d tt)
  (fun=> func pj0) 
  (pj0 ~(d)~> j)
    (fun=> pj0 ~(d)~> (j+1)).
Proof. by do 3 (xwp; xapp). Qed.

End incr1.

Notation "'++' k" :=
  (incr1.func k)
  (in custom trm at level 58, format "++ k") : trm_scope.

Module incr.

Definition func :=
  (<{ fun "real_j" "x" =>
      let "tmp1" = ! "real_j" in
      let "tmp2" = "tmp1" + "x" in
      "real_j" := "tmp2" }>).

Lemma spec (pj0 : loc) (d : D) (j x : int) :
  htriple (single d tt)
  (fun=> func pj0 x) 
  (pj0 ~(d)~> j)
    (fun=> pj0 ~(d)~> (j+x)).
Proof. by do 3 (xwp; xapp). Qed.

End incr.

Notation "k '+=' x" :=
  (incr.func k x)
  (in custom trm at level 58, format "k  +=  x") : trm_scope.

Module index.

Definition whilecond N (i x_ind k : trm) :=
  <{
    let 'k = !k in 
    let "x_ind[k]" = read_array x_ind 'k in 
    let 'c = "x_ind[k]" = i in 
    let 'c = not 'c in
    let 'l = 'k < N in 
    'c && 'l
  }>.


Definition func (N : int) := 
  let loop := While (whilecond N "i" "x_ind" "k") <{++"k"}> in
  <{
    fun "i" "x_ind" =>
      let 'k = ref 0 in 
      loop;
      let "ans" = ! 'k in
      free 'k;
      "ans"
  }>.

Lemma val_int_eq i j : 
  (val_int i = val_int j) = (i = j).
Proof. by extens; split=> [[]|]->. Qed.

Ltac fold' := 
  rewrite ?wp_single ?val_int_eq
    -/(whilecond _ _ _ _) 
    -/(incr _) 
    -/(While_aux _ _) 
    -/(While _ _) //=.

Import List.

Ltac bool_rew := 
  rewrite ?false_eq_isTrue_eq ?true_eq_isTrue_eq -?(isTrue_and, isTrue_not, isTrue_or).


Lemma spec `{Inhab D} d N (i : int) (xind : list int) (x_ind : loc) : 
  htriple (single d tt) 
    (fun=> func N i x_ind)
    (harray_int xind x_ind d \* \[length xind = N :> int] \* \[List.NoDup xind])
    (fun hv => harray_int xind x_ind d \* \[hv = fun=> index i xind]).
Proof with fold'.
  xwp; xsimpl=> ??; xapp=> k...
  set (cond x := isTrue (List.nth (abs x) xind 0 <> i /\ x < N)).
  set (Inv b x := 
    \[b = cond x] \* \[0 <= x <= N] \*
    \[~ In i (take (abs x) xind)] \*
    k d ~(d)~> x \* harray_int xind x_ind d
    ).
  xwp; xwhile1 0 (index i xind) (cond 0) Inv; rewrite /Inv.
  { xsimpl=> ??->??. 
    do 5 (xwp; xapp); xapp=> ?->; xsimpl*.
    rewrite /cond. bool_rew... }
  { move=> x; rewrite /cond; xsimpl*.
    bool_rew; rewrite not_and_eq.
    case: (classicT (x = N)).
    { move=>-> _ _. rewrite in_take; last math.
      move: (index_size i xind); math. }
    move=> ? [/not_not_inv<- ? _|]; last math.
    rewrite index_nodup //; math. }
  { xsimpl*=> {Inv}k; rewrite /cond; bool_rew.
    case=> xindN ??; rewrite in_take; last math.
    suff: (index i xind <> k) by math.
    move=> E; apply/xindN; rewrite -E nth_index // -index_mem; math. }
  { move=> j ? IH; rewrite /cond; bool_rew.
    xsimpl=> -?? T. xwp; xapp incr1.spec; xapp; try math. 
    { eauto. }
    { move: T; rewrite ?in_take; math. }
    rewrite /cond; bool_rew. xsimpl*. }
  { xsimpl*; split=> //; math. }
  { move=> _. xsimpl=> *; do 2 (xwp; xapp); xwp; xval; xsimpl*. }
  exact/indexG0.
Qed.

End index.

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

Module search.

Definition whilecond (p_arr : trm) (pj : trm) (i : trm) :=
  (<{ let "tmp1" = ! pj in
      let "tmp2" = "tmp1" + 1 in
      let "tmp3" = read_array p_arr "tmp2" in
      let "cnd" = "tmp3" <= i in 
      "cnd" }>).

Definition func :=
  let loop := While (whilecond "p_arr" "j" "i") <{ ++ "j" }> in
  <{ fun "i" "p_arr" => let "j" = ref 0 in 
      loop ; 
      let "tmp" = ! "j" in 
      free "j";
      "tmp"
  }>.

Section search_proof.

Context (L : list int) {H : IncreasingIntList L}.
Context {HDInhabit : Inhab D}.

Import List.

Lemma whilecond_spec (j k : int) (pj p_arr : loc) (d : D) :
  htriple (single d tt)
    (fun=> whilecond p_arr pj k)
    (pj ~(d)~> j \* harray_int L p_arr d)
    (fun hv => \[hv d = (Z.leb (List.nth (abs (j+1)) L 0) k)]
      \* pj ~(d)~> j \* harray_int L p_arr d).
Proof.
  intros. apply wp_equiv; do 4 (xwp; xapp).
  xwp; xval; xsimpl.
  f_equal.
  rewrite -> isTrue_eq_if.
  case_if; symmetry; [ apply Z.leb_le | apply Z.leb_gt ]; math.
Qed.

Local Tactic Notation "fold_search" := 
  rewrite ?wp_single
    -/(whilecond _ _ _) 
    -/(incr1.func _) 
    -/(While_aux _ _) 
    -/(While _ _) //.

Lemma spec : forall (d : D) (p_arr : loc) (k : int)
  (Hk : (0 <= k < List.nth (abs (length L - 1)) L 0))
  (a : int) (Ha : (0 <= a < (length L - 1))) 
  (Hka : (List.nth (abs a) L 0 <= k < List.nth (abs (a + 1)) L 0)), 
  htriple (single d tt) 
    (fun=> func k p_arr)
    (harray_int L p_arr d)
    (fun hv => \[hv d = val_int a] \* harray_int L p_arr d).
Proof with fold_search.
  intros.
  apply wp_equiv.
  xwp; xapp=> pj /=...
  remember (pj d) as pj0.
  xwp; xwhile1 0 a (negb (ssrbool.is_left (Z.eq_dec 0 a)))
    (fun b j => \[(0 <= j < (length L - 1)) /\
      (List.nth (abs j) L 0 <= k) /\ b = Z.leb (List.nth (abs (j+1)) L 0) k] 
      \* pj0 ~(d)~> j \* harray_int L p_arr d).
  { intros b j. xsimpl. intros (H1 & H2 & ->).
    xapp whilecond_spec; auto.
    intros ? ->. xsimpl*.
  }
  { intros j. xsimpl*.
    intros (Hj & Hleb & EE).
    symmetry in EE.
    rewrite -> Z.leb_gt in EE.
    eapply search_unify with (L:=L) (j:=k); auto.
  }
  { intros j. xsimpl*.
    intros (Hj & Hleb & EE).
    symmetry in EE.
    rewrite -> Z.leb_le in EE.
    destruct (Z.leb a j) eqn:EE2.
    2: now apply Z.leb_gt in EE2.
    apply Z.leb_le in EE2. 
    assert (a + 1 <= j + 1) as EE2' by math.
    apply IIL_L_inc' with (L:=L) in EE2'; auto; try math.
  }
  { intros j (Hj1 & Hj2) IH.
    xsimpl. intros (_ & H1 & H2).
    apply eq_sym, Z.leb_le in H2.
    xwp. xapp incr1.spec.
    destruct (Z.leb (a-1) j) eqn:Ef.
    { (* check if it is the end *)
      rewrite -> Z.leb_le in Ef.
      assert (j = a - 1) as -> by math.
      replace (a - 1 + 1) with a in * by math.
      xwp; xapp whilecond_spec...
      intros r Er...
      destruct Hka as (_ & Hka).
      rewrite -Z.leb_gt in Hka.
      rewrite -> Hka in Er.
      rewrite Er.
      xwp. xif. 1: intros; by false.
      intros _. 
      xwp. xval.
      xsimpl. split; auto. eqsolve.
    }
    { (* use IH *)
      rewrite -> Z.leb_gt in Ef. clear Hj2.
      assert (j + 1 <= a) as Hj2 by math.
      assert (j < j + 1) as Hj3 by math.
      specialize (IH (j+1) true).
      destruct Hka as (Hka1 & Hka2).
      xapp IH; try math.
      2: intros; xsimpl*.
      { split; try math. split; try assumption. 
        symmetry. apply Z.leb_le.
        transitivity (List.nth (abs a) L 0); try assumption. 
        destruct (Z.leb a (j+1+1)) eqn:EE.
        { rewrite -> Z.leb_le in EE.
          assert (j+1+1 = a) as -> by math.
          reflexivity.
        }
        { rewrite -> Z.leb_gt in EE.
          match goal with |- (?a <= ?b)%Z => enough (a < b); try math end.
          apply IIL_L_inc; math.
        }
      }
    }
  }
  { (* pre *)
    xsimpl. split; try math. destruct Hka as (Hka1 & Hka2). split.
    { transitivity (List.nth (abs a) L 0); try assumption.
      apply IIL_L_inc'; auto; try math.
    }
    { destruct (Z.eq_dec 0 a) as [ <- | ]; simpl.
      { apply eq_sym, Z.leb_gt; math. }
      { apply eq_sym, Z.leb_le.
        transitivity (List.nth (abs a) L 0); try assumption.
        apply IIL_L_inc'; auto; math.
      }
    }
  }
  { (* post *)
    xsimpl. intros _ (_ & H1 & H2).
    symmetry in H2. rewrite -> Z.leb_gt in H2.
    xwp. xapp. xwp. xapp. xwp. xval.
    xsimpl*.
  }
Qed.

End search_proof.

End search. 

