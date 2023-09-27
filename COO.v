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

Lemma hstar_fset_label_single (x : D) : 
hbig_fset hstar (single x tt) = @^~ x.
Proof. 
apply/fun_ext_1=> ?.
rewrite update_empty hbig_fset_update // hbig_fset_empty. xsimpl*. Qed.

Hint Rewrite hstar_fset_label_single hstar_fset_Lab : hstar_fset.


Section pure_index.

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


End pure_index.


Module index.

Definition and :=
  <{
    fun 'b 'c =>
    if 'b then 'c 
    else false
  }>.

Lemma and_spec (b c : bool) d : 
  htriple (single d tt) 
    (fun=> and b c)
    \[]
    (fun hr => \[hr d = b && c]).
Proof.
  xwp; xif=> bp; xwp; xval; xsimpl.
  all: by case: c b bp=> -[].
Qed.

Definition whilecond N (i x_ind k : trm) :=
  <{
    let 'k = !k in 
    let "x_ind[k]" = read_array x_ind 'k in 
    let 'c = "x_ind[k]" = i in 
    let 'c = not 'c in
    let 'l = 'k < N in 
    and 'c 'l
  }>.

Definition incr :=
  (<{ fun "real_j" =>
      let "tmp1" = ! "real_j" in
      let "tmp2" = "tmp1" + 1 in
      "real_j" := "tmp2" }>).


Definition func (N : int) := 
  let loop := While (whilecond N "i" "x_ind" "k") (incr "k") in
  <{
    fun "i" "x_ind" =>
      let 'k = ref 0 in 
      loop;
      let "ans" = ! 'k in
      free 'k;
      "ans"
  }>.

Lemma incr_spec (pj0 : loc) (d : D) (j : int) :
  htriple (single d tt)
  (fun=> incr pj0) 
  (pj0 ~(d)~> j)
    (fun=> pj0 ~(d)~> (j+1)).
Proof. by do 3 (xwp; xapp). Qed.

Lemma wp_single d t Q : 
  wp (single d tt) t Q = 
  wp (single d tt) (fun=> t d) Q.
Proof. by apply/wp_ht_eq=> ? /[! indom_single_eq]->. Qed.

Lemma val_int_eq i j : 
  (val_int i = val_int j) = (i = j).
Proof. by extens; split=> [[]|]->. Qed.

Ltac fold' := 
  rewrite ?wp_single ?val_int_eq
    -/(whilecond _ _ _ _) 
    -/(incr _) 
    -/(While_aux _ _) 
    -/(While _ _) //=.

Ltac xwhile Z N b Inv := 
  let N := constr:(N) in
  let Z := constr:(Z) in 
  let Inv' := constr:(Inv) in
  xseq_xlet_if_needed; xstruct_if_needed;
  eapply (wp_while_unary Inv b (Z := Z) (N := N)); autos*.

Hint Resolve htriple_array_read : htriple.

Notation "x '[' i ']'" := (List.nth (abs i) x 0) (at level 50, format "x [ i ]").

Import List.

Ltac bool_rew := 
  rewrite ?false_eq_isTrue_eq ?true_eq_isTrue_eq -?(isTrue_and, isTrue_not, isTrue_or).

(*
  bool --> Prop in Inv
*)

Lemma spec `{Inhab D} d N (i : int) (xind : list int) (x_ind : loc) : 
  htriple (single d tt) 
    (fun=> func N i x_ind)
    (harray_int xind x_ind d \* \[length xind = N :> int] \* \[List.NoDup xind])
    (fun hv => harray_int xind x_ind d \* \[hv d = index i xind]).
Proof with fold'.
  xwp; xsimpl=> ??; xapp=> k...
  set (cond x := isTrue (List.nth (abs x) xind 0 <> i /\ x < N)).
  set (Inv b x := 
    \[b = cond x /\ 0 <= x <= N] \*
    \[~ In i (take (abs x) xind)] \*
      k d ~(d)~> x \*
      harray_int xind x_ind d
    ).
  xwp; xwhile 0 (index i xind) (cond 0) Inv; rewrite /Inv.
  { xsimpl=> ?? -[->]??. 
    do 5 (xwp; xapp); xapp and_spec=> ?->; xsimpl*.
    rewrite /cond. bool_rew... }
  { move=> x; rewrite /cond. xsimpl*.
    bool_rew; rewrite not_and_eq=> -[].
    case: (classicT (x = N)).
    { move=>-> _ _. rewrite in_take; last math.
      move: (index_size i xind); math. }
    move=> ? [/not_not_inv<- ? _|]; last math.
    rewrite index_nodup //; math. }
  { xsimpl*=> {Inv}k []; rewrite /cond; bool_rew.
    case=> xindN ??.
    rewrite in_take; last math.
    suff: (index i xind <> k) by math.
    move=> E; apply/xindN; rewrite -E nth_index // -index_mem; math. }
  { move=> j ? IH; rewrite /cond; bool_rew.
    xsimpl=> -[][]??? T. xwp; xapp incr_spec; xapp. 
    { split; [reflexivity|math]. }
    { move: T; rewrite ?in_take; math. }
    { math. }
    rewrite /cond; bool_rew. xsimpl*. }
  { xsimpl*; split=> //; math. }
  { move=> _. xsimpl=> *; do 2 (xwp; xapp); xwp; xval; xsimpl*. }
  exact/indexG0.
Qed.


End index.