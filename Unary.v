Set Implicit Arguments.
From SLF Require Import Fun LabType ListCommon Prelude.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

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

Global Hint Resolve and.spec : htriple.

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

Module min.
Section min.

Context {D : Type}.

Definition func :=
  <{fun "b" "c" =>
    let "cnd" = "b" < "c" in 
    if "cnd" then "b" else "c"
  }>.

Lemma spec `{Inhab D} (b c : int) d : 
  @htriple D (single d tt) 
    (fun=> func b c)
    \[]
    (fun hr => \[hr = fun d=> Z.min b c]).
Proof.
  xwp;xapp; xwp; xif=> ?; xwp; xval; xsimpl; extens=>?;f_equal; lia.
Qed.
End min.
End min.

Hint Resolve min.spec : lhtriple.

Module index_bounded.
Section index_bounded.

Definition func := Eval cbn zeta beta in
  let whilecond N (i x_ind k : trm) := <{
    let 'k = !k in 
    let "x_ind[k]" = read_array x_ind 'k in 
    let 'c = "x_ind[k]" = i in 
    let 'c = not 'c in
    let 'l = 'k < N in 
    'c && 'l
  }> in
  let loop := While (whilecond "rb" "i" "x_ind" "k") <{++"k"}> in
  <{
    fun "lb" "rb" "i" "x_ind" =>
      let 'k = ref "lb" in 
      loop;
      let "ans" = ! 'k in
      free 'k;
      "ans"
  }>.

Ltac fold' := 
  rewrite ?wp_single ?val_int_eq
    -/(While_aux _ _) 
    -/(While _ _) //=.

Import List list_interval_notation.

Lemma spec {D} `{Inhab D} d N (lb rb i : int) (xind : list int) (x_ind : loc) : 
  @htriple D (single d tt) 
    (fun=> func lb rb i x_ind)
    (harray_int xind x_ind d \* \[length xind = N :> int] 
      \* \[List.NoDup (xind [[ lb -- rb ]])] 
      \* \[0 <= lb <= rb] \* \[rb <= N])
    (fun hv => harray_int xind x_ind d \* \[hv = fun=> lb + ListCommon.index i (xind [[ lb -- rb ]])]).
Proof with fold'.
  set (xind_sub := xind [[ lb -- rb ]]).
  set (N_sub := rb - lb).
  xwp; xsimpl=> ????; xapp=> k...
  assert (length xind_sub = rb - lb :> int) by (subst xind_sub N; now rewrite list_interval_length). 
  set (cond x := isTrue (List.nth (abs x) xind_sub 0 <> i /\ x < N_sub)).
  set (Inv b x := 
    \[b = cond x] \* \[0 <= x <= N_sub] \*
    \[~ In i (take (abs x) xind_sub)] \*
    k d ~(d)~> (lb + x) \* harray_int xind x_ind d
    ).
  xwp; xwhile1 0 (ListCommon.index i xind_sub) (cond 0) Inv; rewrite /Inv.
  { xsimpl=> ??->??.
    do 5 (xwp; xapp); xapp=> ?->; xsimpl*.
    rewrite /cond /xind_sub /N_sub. bool_rew.
    f_equal. rew_bool_eq.
    subst N_sub. split; intros (? & ?); split; try math.
    { rewrite <- list_interval_nth; try math; congruence. }
    { rewrite <- list_interval_nth in *; try math; congruence. }
  }
  { move=> x; rewrite /cond; xsimpl*.
    bool_rew; rewrite not_and_eq.
    case: (classicT (x = N_sub)).
    { move=>-> _ _. rewrite in_take; eauto; last math.
      move: (index_size i xind_sub); math. }
    move=> ? [/not_not_inv<- ? _|]; last math.
    rewrite index_nodup //; math. }
  { xsimpl*=> {Inv}k; rewrite /cond; bool_rew.
    case=> xindN ??; rewrite in_take; eauto; last math.
    suff: (ListCommon.index i xind_sub <> k) by math.
    move=> E; apply/xindN; rewrite -E nth_index // -index_mem; eauto; math. }
  { move=> j ? IH; rewrite /cond; bool_rew.
    xsimpl=> -?? T. xwp; xapp (@incr1.spec _ H).  
    replace (lb + j + 1) with (lb + (j + 1)) by math.
    xapp; try math.
    { eauto. }
    { move: T; rewrite ?in_take; eauto; math. }
    rewrite /cond; bool_rew. xsimpl*. }
  { replace (lb + 0) with lb by math. 
    xsimpl*; split=> //; math. }
  { move=> _. xsimpl=> *; do 2 (xwp; xapp); xwp; xval; xsimpl*. }
  exact/indexG0.
Qed.

End index_bounded.
End index_bounded.

Module index.
Section index.

Definition func (N : int) := index_bounded.func 0 N.

Import List.

Lemma spec {D : Type} `{Inhab D} (d : D) (N : int) (i : int) (xind : list int) (x_ind : loc) : 
  htriple (single d tt) 
    (fun=> func N i x_ind)
    (harray_int xind x_ind d \* \[length xind = N :> int] \* \[List.NoDup xind])
    (fun hv => harray_int xind x_ind d \* \[hv = fun=> ListCommon.index i xind]).
Proof.
  apply wp_equiv. xapp @index_bounded.spec=> * //; try math.
  all: subst N.
  1: rewrite slice_fullE //.
  rewrite -> slice_fullE, -> Z.add_0_l in * |-. xsimpl*.
Qed.

Lemma Spec (fs : fset int) N l (xind : list int) (x_ind : loc) (f : int -> int) : 
  htriple ⟨l, fs⟩
    (fun i => func N (f (el i)) x_ind)
    ((\*_(d <- fs) harray_int xind x_ind (Lab l d)) \* \[length xind = N :> int] \* \[List.NoDup xind])
    (fun hv => (\*_(d <- fs) harray_int xind x_ind (Lab l d)) \* \[hv = fun i => ListCommon.index (f (el i)) xind]).
Proof.
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

Definition func (N : int) := Eval cbn zeta beta in
  let whilecond N (i j x y k : trm) :=
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
  }> in
  let loop := While (whilecond N "i" "j" "x" "y" "k") <{++"k"}> in
  <{
    fun "i" "j" "x" "y" =>
      let 'k = ref 0 in 
      loop;
      let "ans" = ! 'k in
      free 'k;
      "ans"
  }>.

Ltac fold' := 
  rewrite ?wp_single ?val_int_eq
    -/(While_aux _ _) 
    -/(While _ _) //=.

Import List.

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

Definition func := Eval cbn beta zeta in
  let whilecond (p_arr : trm) (pj : trm) (i : trm) :=
  <{ let "tmp1" = ! pj in
      let "tmp2" = "tmp1" + 1 in
      let "tmp3" = read_array p_arr "tmp2" in
      let "cnd" = "tmp3" <= i in 
      "cnd" }> in
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

Local Tactic Notation "fold_search" := 
  rewrite ?wp_single ?val_int_eq
    -/(incr1.func _) 
    -/(While_aux _ _) 
    -/(While _ _) //.

Lemma spec (d : D) (p_arr : loc) (k : int)
  (Hk : (0 <= k < L[length L - 1]))
  (a : int) (Ha : (0 <= a < (length L - 1))) 
  (Hka : (L[a] <= k < L[a + 1])) :
  htriple (single d tt) 
    (fun=> func k p_arr)
    (harray_int L p_arr d)
    (fun hv => \[hv = fun=> val_int a] \* harray_int L p_arr d).
Proof with fold_search.
  xwp; xapp=> pj /=...
  remember (pj d) as pj0.
  xwp; xwhile1 0 a (negb (ssrbool.is_left (Z.eq_dec 0 a)))
    (fun b j => \[(0 <= j < (length L - 1)) /\
      (L[j] <= k) /\ b = Z.leb L[j+1] k] 
      \* pj0 ~(d)~> j \* harray_int L p_arr d).
  { intros b j. xsimpl. intros (H1 & H2 & ->).
    do 4 (xwp; xapp). xwp; xval; xsimpl*.
    rewrite isTrue_eq_if. 
    destruct ((L[j + 1] <=? k)) eqn:E; rewrite ?Z.leb_le ?Z.leb_gt in E; case_if; try eqsolve; try math. }
  { intros j. xsimpl*. intros (Hj & Hleb & EE%eq_sym%Z.leb_gt).
    eapply search_unify with (L:=L) (j:=k); auto. }
  { intros j. xsimpl*. intros (Hj & Hleb & EE%eq_sym%Z.leb_le).
    destruct (Z.leb a j) eqn:EE2; rewrite ?Z.leb_le ?Z.leb_gt in EE2; try math.
    assert (a + 1 <= j + 1) as EE2' by math.
    apply IIL_L_inc' with (L:=L) in EE2'; auto; try math. }
  { intros j (Hj1 & Hj2) IH. xsimpl. intros (_ & H1 & H2%eq_sym%Z.leb_le).
    xwp. xapp (@incr1.spec).
    destruct (Z.leb (a-1) j) eqn:Ef; rewrite ?Z.leb_le ?Z.leb_gt in Ef.
    { (* check if it is the end *)
      assert (j = a - 1) as -> by math.
      replace (a - 1 + 1) with a in * by math.
      xwp; xlet. do 4 (xwp; xapp). xwp; xval; xsimpl*. xwp; xif=> C; try math.
      xwp; xval; xsimpl*.
      rewrite -?Z.leb_le in C. eqsolve. }
    { (* use IH *)
      clear Hj2.
      assert (j + 1 <= a) as Hj2 by math.
      assert (j < j + 1) as Hj3 by math.
      specialize (IH (j+1) true).
      destruct Hka as (Hka1 & Hka2).
      xapp IH; try math.
      2: intros; xsimpl*.
      split; try math. split; try assumption. 
      symmetry. apply Z.leb_le.
      transitivity (L[a]); try assumption. 
      destruct (Z.leb a (j+1+1)) eqn:EE; rewrite ?Z.leb_le ?Z.leb_gt in EE.
      { assert (j+1+1 = a) as -> by math. reflexivity. }
      { apply IIL_L_inc'; auto; math. } } }
  { xsimpl. split; try math. destruct Hka as (Hka1 & Hka2). split.
    { transitivity (L[a]); try assumption.
      apply IIL_L_inc'; auto; try math. }
    { destruct (Z.eq_dec 0 a) as [ <- | ]; simpl.
      { apply eq_sym, Z.leb_gt; math. }
      { apply eq_sym, Z.leb_le.
        transitivity (L[a]); try assumption.
        apply IIL_L_inc'; auto; math. } } }
  { xsimpl. intros _ (_ & H1 & H2%eq_sym%Z.leb_gt).
    do 2 (xwp; xapp). xwp. xval. xsimpl*. }
Qed.

End search_proof.

End search. 
End search. 

