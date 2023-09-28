Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct.
From SLF Require Import Fun LabType.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Module NatDom : Domain with Definition type := nat.
Definition type := nat.
End NatDom.

Module IntDom : Domain with Definition type := int.
Definition type := int.
End IntDom.

Module Export AD := WithArray(IntDom).
Check eq_refl : D = labeled int.

Global Instance Inhab_D : Inhab D. 
Proof Build_Inhab (ex_intro (fun=> True) (Lab (0, 0) 0) I).

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

Notation "x '[' i ']'" := (List.nth (abs i) x 0) (at level 50, format "x [ i ]").

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

