Set Implicit Arguments.
From SLF Require Import Fun LabType ListCommon.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

(* Module NatDom : Domain with Definition type := nat.
Definition type := nat.
End NatDom.

Module IntDom : Domain with Definition type := int.
Definition type := int.
End IntDom.

Module Int2Dom : Domain with Definition type := (int * int)%type.
Definition type := (int * int)%type.
End Int2Dom. *)



(* Section WithUnary. *)

(* Context `{Inhab D}. *)

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

Module and.

Section and.

Context {D : Type}.

Implicit Type d : D.

Definition func :=
  <{fun 'b 'c =>
    if 'b then 'c 
    else false
  }>.

Lemma spec `{Inhab D} (b c : bool) d : 
  htriple (single d tt) 
    (fun=> func b c)
    \[]
    (fun hr => \[hr d = b && c]).
Proof.
  xwp; xif=> bp; xwp; xval; xsimpl.
  all: by case: c b bp=> -[].
Qed.

End and.

End and.

Notation "t1 && t2" :=
  (and.func t1 t2)
  (in custom trm at level 58) : trm_scope.

Hint Resolve and.spec : htriple.

Module incr1.

Section incr1. 

Context {D : Type} `{Inhab D}.

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
End incr1.

Notation "'++' k" :=
  (incr1.func k)
  (in custom trm at level 58, format "++ k") : trm_scope.

Module incr.

Section incr. 

Context {D : Type}.

Definition func :=
  (<{ fun "real_j" "x" =>
      let "tmp1" = ! "real_j" in
      let "tmp2" = "tmp1" + "x" in
      "real_j" := "tmp2" }>).

Lemma spec `{Inhab D} (pj0 : loc) (d : D) (j x : int) :
  htriple (single d tt)
  (fun=> func pj0 x) 
  (pj0 ~(d)~> j)
    (fun=> pj0 ~(d)~> (j+x)).
Proof. by do 3 (xwp; xapp). Qed.

End incr.
End incr.

Notation "k '+=' x" :=
  (incr.func k x)
  (in custom trm at level 58, format "k  +=  x") : trm_scope.

Module index.
Section index.

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

Lemma spec {D : Type} `{Inhab D} (d : D) N (i : int) (xind : list int) (x_ind : loc) : 
  htriple (single d tt) 
    (fun=> func N i x_ind)
    (harray_int xind x_ind d \* \[length xind = N :> int] \* \[List.NoDup xind])
    (fun hv => harray_int xind x_ind d \* \[hv = fun=> ListCommon.index i xind]).
Proof with fold'.
  xwp; xsimpl=> ??; xapp=> k...
  set (cond x := isTrue (List.nth (abs x) xind 0 <> i /\ x < N)).
  set (Inv b x := 
    \[b = cond x] \* \[0 <= x <= N] \*
    \[~ In i (take (abs x) xind)] \*
    k d ~(d)~> x \* harray_int xind x_ind d
    ).
  xwp; xwhile1 0 (ListCommon.index i xind) (cond 0) Inv; rewrite /Inv.
  { xsimpl=> ??->??.
    do 5 (xwp; xapp); xapp=> ?->; xsimpl*.
    rewrite /cond. bool_rew... }
  { move=> x; rewrite /cond; xsimpl*.
    bool_rew; rewrite not_and_eq.
    case: (classicT (x = N)).
    { move=>-> _ _. rewrite in_take; eauto; last math.
      move: (index_size i xind); math. }
    move=> ? [/not_not_inv<- ? _|]; last math.
    rewrite index_nodup //; math. }
  { xsimpl*=> {Inv}k; rewrite /cond; bool_rew.
    case=> xindN ??; rewrite in_take; eauto; last math.
    suff: (ListCommon.index i xind <> k) by math.
    move=> E; apply/xindN; rewrite -E nth_index // -index_mem; eauto; math. }
  { move=> j ? IH; rewrite /cond; bool_rew.
    xsimpl=> -?? T. xwp; xapp (@incr1.spec _ H); xapp; try math. 
    { eauto. }
    { move: T; rewrite ?in_take; eauto; math. }
    rewrite /cond; bool_rew. xsimpl*. }
  { xsimpl*; split=> //; math. }
  { move=> _. xsimpl=> *; do 2 (xwp; xapp); xwp; xval; xsimpl*. }
  exact/indexG0.
Qed.

Lemma Spec (fs : fset int) N l (xind : list int) (x_ind : loc) (f : int -> int) : 
  htriple ⟨l, fs⟩
    (fun i => func N (f (el i)) x_ind)
    ((\*_(d <- fs) harray_int xind x_ind (Lab l d)) \* \[length xind = N :> int] \* \[List.NoDup xind])
    (fun hv => (\*_(d <- fs) harray_int xind x_ind (Lab l d)) \* \[hv = fun i => ListCommon.index (f (el i)) xind]).
Proof with fold'.
  apply/htriple_conseq. 1: apply htriple_val_eq. 2-3: xsimpl*.
  apply wp_equiv. xsimpl*. intros. apply wp_equiv.
  apply/htriple_conseq. 3: hnf=> hv; rewrite -hstar_fset_pure. 2-3: rewrite -hstar_fset_Lab -?hbig_fset_hstar; xsimpl*. 
  apply/htriple_union_pointwise=> [> -> //|].
  intros. rewrite -wp_equiv wp_single /=. 
  xapp (@spec)=> //.
  xsimpl*.
Qed.

End index.
End index.

Module index2.

Section index2. 

Context {D : Type} `{Inhab D}.

Definition whilecond N (i j x y k : trm) :=
  <{
    let 'k = !k in 
    let "x[k]" = x['k] in 
    let "y[k]" = y['k] in 
    let "x[k] = i" = "x[k]" = i in 
    let "y[k] = j" = "y[k]" = j in 
    let "x[k] = i && y[k] = j" = "x[k] = i" && "y[k] = j" in
    let "!(x[k] = i && y[k] = j)" = not "x[k] = i && y[k] = j" in
    let "k < N" = 'k < N in 
      "!(x[k] = i && y[k] = j)" && "k < N"
  }>.

Definition func (N : int) := 
  let loop := While (whilecond N "i" "j" "x" "y" "k") <{++"k"}> in
  <{
    fun "i" "j" "x" "y" =>
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
    -/(whilecond _ _ _ _ _ _) 
    -/(incr _) 
    -/(While_aux _ _) 
    -/(While _ _) //=.

Import List.

Ltac bool_rew := 
  rewrite ?false_eq_isTrue_eq ?true_eq_isTrue_eq -?(isTrue_and, isTrue_not, isTrue_or).

Hint Resolve and.spec : htriple.

Implicit Type d : D.

Lemma spec d N (i j : int) (xind yind : list int) (x_ind y_ind : loc) : 
  htriple (single d tt) 
    (fun=> func N i j x_ind y_ind)
    (harray_int xind x_ind d \*
     harray_int yind y_ind d \*
     \[length xind = N :> int] \*
     \[length yind = N :> int] \* \[List.NoDup (combine xind yind)])
    (fun hv => \[hv = fun=> ListCommon.index (i, j) (combine xind yind)] \* harray_int xind x_ind d \* harray_int yind y_ind d).
Proof with fold'.
xwp; xsimpl=> ???; xapp=> k...
have ?: Datatypes.length (combine xind yind) = N :> int by rewrite combine_length; lia.
set (cond x := isTrue (List.nth (abs x) (combine xind yind) (0,0) <> (i,j) /\ x < N)).
set (Inv b x := 
  \[b = cond x] \* \[0 <= x <= N] \*
  \[~ In (i,j) (take (abs x) (combine xind yind))] \*
  k d ~(d)~> x \* harray_int xind x_ind d \*  harray_int yind y_ind d
  ).
xwp; xwhile1 0 (ListCommon.index (i,j) (combine xind yind)) (cond 0) Inv; rewrite /Inv.
{ xsimpl=> ??->??.
  do 6 (xwp; xapp); move=> ?... 
  move->; do 2 (xwp; xapp).
  xapp=> ?->; xsimpl*.
  rewrite /cond combine_nth; last lia. 
  bool_rew... do ? f_equal; extens. by rewrite pair_equal_spec. }
{ move=> x; rewrite /cond; xsimpl*.
  bool_rew; rewrite not_and_eq.
  case: (classicT (x = N)).
  { move=>-> _ _; rewrite in_take //; last lia.
    move: (index_size (i,j) (combine xind yind)); lia. }
  move=> ? [/not_not_inv<- ? _|]; last math.
  rewrite index_nodup //; math. }
{ xsimpl*=> {Inv}k; rewrite /cond; bool_rew.
  case=> xindN ??; rewrite in_take; eauto; last math.
  suff: (ListCommon.index (i, j) (combine xind yind) <> k) by lia.
  move=> E; apply/xindN; rewrite -E nth_index // -index_mem; eauto; math. }
{ move=> ?? IH; rewrite /cond; bool_rew...
  xsimpl=> -?? T. xwp; xapp (@incr1.spec _ H); xapp; try math. 
  { eauto. }
  { move: T; rewrite ?in_take; eauto; math. }
  rewrite /cond; bool_rew. xsimpl*. }
{ xsimpl*; split=> //; math. }
{ move=> _. xsimpl=> *; do 2 (xwp; xapp); xwp; xval; xsimpl*. }
exact/indexG0.
Qed.

End index2.
End index2.

Module search.
Section search.

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

Context (L : list int) {D :Type} {H : IncreasingIntList L}.
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
    (fun hv => \[hv = fun=> val_int a] \* harray_int L p_arr d).
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
    xwp. xapp (@incr1.spec _ HDInhabit).
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
End search. 

