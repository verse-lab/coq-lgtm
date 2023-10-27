Set Implicit Arguments.
From SLF Require Import Fun LabType.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.


(* Module WithUnary (Dom : Domain). *)


(* Module Export AD := WithLoops(Dom). *)

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

Global Instance Inhab_lab_int : Inhab (labeled int).
split. by exists (Lab (0,0) 0). Qed.


Section pure_facts.

Context {A : Type}.

Implicit Type l s : list A.
(* Implicit Type i : A. *)

Export List.

Definition index (i : A) l : int. 
Proof using.
Admitted.
Lemma index_nodup (def : A) i l : 
  0 <= i < length l ->
  List.NoDup l -> 
    index (nth (abs i) l def) l = i.
Proof.
Admitted.

Lemma in_take x l i : 0 <= i <= length l -> (In x (take (abs i) l)) = (index x l < i).
Proof.
Admitted.

Lemma nth_index (def : A) x s : In x s -> nth (abs (index x s)) s def = x.
Admitted.

Lemma index_mem x s : (index x s < length s) = (In x s).
Admitted.

Lemma index_size x s : index x s <= length s.
Proof. Admitted.

Lemma indexG0 x s : 0 <= index x s.
Proof. Admitted.

Lemma memNindex x s :  ~In x s -> index x s = length s.
Admitted.

Definition list_interval (lb rb : nat) l :=
  take (rb - lb)%nat (drop lb l).

Lemma list_interval_length (lb rb : int) l :
  0 <= lb <= rb -> rb <= length l -> length (list_interval (abs lb) (abs rb) l) = rb - lb :> int.
Admitted.

Lemma list_interval_nth (def : A) (x lb rb : int) l :
  0 <= lb <= rb -> rb <= length l -> 0 <= x < rb - lb ->
  nth (abs (lb + x)) l def = nth (abs x) (list_interval (abs lb) (abs rb) l) def.
Admitted.

End pure_facts.

Module and.
Section and.

Context {D : Type}.

Definition func :=
  <{fun 'b 'c =>
    if 'b then 'c 
    else false
  }>.

Lemma spec `{Inhab D} (b c : bool) d : 
  @htriple D (single d tt) 
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

Definition func :=
  (<{ fun "real_j" =>
      let "tmp1" = ! "real_j" in
      let "tmp2" = "tmp1" + 1 in
      "real_j" := "tmp2" }>).

Lemma spec {D} `{Inhab D} (pj0 : loc) (d : D) (j : int) :
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

Lemma spec {D} `{Inhab D} (pj0 : loc) (d : D) (j x : int) :
  htriple (single d tt)
  (fun=> func pj0 x) 
  (pj0 ~(d)~> j)
    (fun=> pj0 ~(d)~> (j+x)).
Proof. by do 3 (xwp; xapp). Qed.

End incr.

Notation "k '+=' x" :=
  (incr.func k x)
  (in custom trm at level 58, format "k  +=  x") : trm_scope.

Module index_bounded.

Definition whilecond N (i x_ind k : trm) :=
  <{
    let 'k = !k in 
    let "x_ind[k]" = read_array x_ind 'k in 
    let 'c = "x_ind[k]" = i in 
    let 'c = not 'c in
    let 'l = 'k < N in 
    'c && 'l
  }>.


Definition func := 
  let loop := While (whilecond "rb" "i" "x_ind" "k") <{++"k"}> in
  <{
    fun "lb" "rb" "i" "x_ind" =>
      let 'k = ref "lb" in 
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

Lemma spec {D} `{Inhab D} d N (lb rb i : int) (xind : list int) (x_ind : loc) : 
  @htriple D (single d tt) 
    (fun=> func lb rb i x_ind)
    (harray_int xind x_ind d \* \[length xind = N :> int] 
      \* \[List.NoDup (list_interval (abs lb) (abs rb) xind)] 
      \* \[0 <= lb <= rb] \* \[rb <= N])
    (fun hv => harray_int xind x_ind d \* \[hv = fun=> lb + index i (list_interval (abs lb) (abs rb) xind)]).
Proof with fold'.
  set (xind_sub := list_interval (abs lb) (abs rb) xind).
  set (N_sub := rb - lb).
  xwp; xsimpl=> ????; xapp=> k...
  assert (length xind_sub = rb - lb :> int) by (subst xind_sub N; now rewrite list_interval_length). 
  set (cond x := isTrue (List.nth (abs x) xind_sub 0 <> i /\ x < N_sub)).
  set (Inv b x := 
    \[b = cond x] \* \[0 <= x <= N_sub] \*
    \[~ In i (take (abs x) xind_sub)] \*
    k d ~(d)~> (lb + x) \* harray_int xind x_ind d
    ).
  xwp; xwhile1 0 (index i xind_sub) (cond 0) Inv; rewrite /Inv.
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
    suff: (index i xind_sub <> k) by math.
    move=> E; apply/xindN; rewrite -E nth_index // -index_mem; eauto; math. }
  { move=> j ? IH; rewrite /cond; bool_rew.
    xsimpl=> -?? T. xwp; xapp (@incr1.spec _ H).  
    replace (lb + j + 1) with (lb + (j + 1)) by math. (* otherwise xapp will fail to instantiate j' *)
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

