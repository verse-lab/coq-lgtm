Set Implicit Arguments.
From SLF Require Import Fun LabType.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops Unary.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Section list_of_fun.

Import List.

(* some customized theory of from functions to lists *)
Lemma list_of_fun [A : Type] [def : A] (f : int -> A) (n : int) (H : 0 <= n) :
  @sigT (list A) (fun l =>
    (length l = n :> int /\ (forall i : int, 0 <= i < n -> nth (abs i) l def = f i))).
Proof.
  remember (abs n) as nn eqn:E.
  revert n H E. induction nn as [ | nn IH ]; intros.
  { assert (n = 0) as -> by math. exists (@nil A). split; auto. intros; math. }
  { assert (nn = abs (n - 1)) as Hq by math. apply IH in Hq; try math.
    destruct Hq as (la & H1 & H2). exists (app la (f (n - 1) :: nil)).
    rewrite -> app_length. split; simpl; try math.
    intros i Hin. destruct (Z.leb (n - 1) i) eqn:E2.
    { apply Z.leb_le in E2. replace i with (n-1) in * by math. 
      replace (abs (n-1)) with (length la) by math. now rewrite nth_middle. }
    { apply Z.leb_gt in E2. rewrite app_nth1. 1: apply H2. all: math. } }
Qed.

Definition list_of_fun' [A : Type] [def : A] (f : int -> A) (n : int) :
  @sigT (list A) (fun l =>
    (length l = abs n :> int /\ (forall i : int, 0 <= i < abs n -> nth (abs i) l def = f i))).
apply list_of_fun. math. Defined.

Fact lof_make_constfun [A : Type] [def : A] (c : A) (n : int) :
  (projT1 (@list_of_fun' _ def (fun=> c) n)) = repeat c (abs n).
Proof.
  destruct (list_of_fun' _ _) as (l & Hlen & HH). simpl.
  apply nth_ext with (d:=def) (d':=def).
  1: rewrite repeat_length; math.
  intros i Hi. rewrite -> nth_indep with (l:=repeat _ _) (d':=c) by (rewrite repeat_length; math).
  rewrite -> nth_repeat, <- HH with (i:=i); try math.
  f_equal; math.
Qed.

(* TODO possibly change this name? *)
Definition lof f N := projT1 (@list_of_fun' int 0 f N).

Lemma nth_lof f N i : 
  0 <= i < abs N -> nth (abs i) (lof f N) 0 = f i.
Proof. unfold lof. destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl. auto. Qed.

Lemma nth_lof' f N i :
  0 <= N -> 0 <= i < N -> nth (abs i) (lof f N) 0 = f i.
Proof. intros ??. apply nth_lof. math. Qed.

Lemma length_lof f N : 
  0 <= N -> length (lof f N) = N :> int.
Proof. unfold lof. destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl. math. Qed.

Lemma length_lof' f N : 
  length (lof f N) = abs N :> nat.
Proof. unfold lof. destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl. math. Qed.

Lemma lof_indices {A : Type} [a : A] (f : int -> A) (g : int -> int) n :
  projT1 (@list_of_fun' _ a (f \o g) n) = List.map f (lof g n).
Proof.
  destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
  pose proof (length_lof' g n) as Hlen2.
  apply (List.nth_ext _ _ a a). 
  1: rewrite List.map_length; math.
  intros n0 Hlt. replace n0 with (abs n0) by math.
  rewrite Hl1 ?(Eval.nth_map_lt 0) ?nth_lof //; try math.
Qed.

Corollary lof_indices' {A : Type} [a : A] (f : int -> A) n :
  projT1 (@list_of_fun' _ a f n) = List.map f (lof id n).
Proof. by rewrite <- lof_indices with (a:=a). Qed.

End list_of_fun.

Definition harray_fun {D : Type} (f:int -> val) (p:loc) (n:int) (d : D) : hhprop D :=
  harray (projT1 (@list_of_fun' _ val_uninit f n)) p d.

Definition harray_fun_int {D : Type} (f:int -> int) (p:loc) (n:int) (d : D) : hhprop D :=
  harray_int (lof f n) p d.

Definition harray_fun_float {D : Type} (f:int -> binary64) (p:loc) (n:int) (d : D) : hhprop D :=
  harray_float (projT1 (@list_of_fun' _ float_unit f n)) p d.

Section memset_alloc.

Variable (a : val).

Definition memset : val := Eval cbn zeta beta in
  let whilecond (i len : trm) := <{ let 'o = ! i in let 'c = 'o < len in 'c }> in
  let loopbody (p i : trm) := 
    <{ let 'o = ! i in
       val_array_set p 'o a;
       ++ i }> in
  let loop := While (whilecond "i" "l") (loopbody "p" "i") in
  <{ fun 'p =>
      let 'l = val_length 'p in
      let 'i = ref 0 in 
      loop; 
      free 'i }>.

Ltac fold' := 
  rewrite ?wp_single ?length_List_length
    -/(incr1.func _) 
    -/(While_aux _ _) 
    -/(While _ _) //=.

Import List.

Fact list_update_intermediate (L : list val) (i : int) (H : 0 <= i < length L) :
  (List.app (repeat a (abs (i+1))) (skipn (abs (i+1)) L)) =
  LibList.update (abs i) a (List.app (repeat a (abs i)) (skipn (abs i) L)).
Admitted.

Lemma htriple_memset_unary {D : Type} `{Inhab D} (L : list val) (p : loc) (d : D) :
  htriple (single d tt) (fun=> memset p)
    (harray L p d) 
    (fun=> harray_fun (fun=> a) p (length L) d).
Proof with fold'.
  xwp; xapp (@htriple_array_length)...
  xwp; xapp=> s...
  remember (s d) as s0 eqn:Es0. (* ? *)
  xwp; xwhile1 0 (length L) (match L with nil => false | _ => true end)
    (fun (b : bool) (i : int) => \[i <= (length L) /\ Z.ltb i (length L) = b] \*
      s0 ~(d)~> i \* 
      harray (List.app (repeat a (abs i)) (skipn (abs i) L)) p d); try math.
  { intros b i. xsimpl. intros (Hi & Eb).
    do 2 (xwp; xapp). xwp. xval. xsimpl*. rewrite isTrue_eq_if.
    case_if; rewrite <- ? Z.ltb_ge, <- ? Z.ltb_lt, -> ? Eb in *; by destruct b. }
  { intros i. xsimpl*. rewrite Z.ltb_ge. math. }
  { intros i. xsimpl*. rewrite Z.ltb_lt. math. }
  { intros i Hii IH. xsimpl*=>_.
    xwp. xseq. xwp; xapp. 
    xwp; xapp (@htriple_array_set)...
    1:{ intros _ _... rewrite app_length repeat_length skipn_length; math. }
    xapp @incr1.spec.
    rewrite -list_update_intermediate; try math.
    xapp IH; try math.
    1: split; [ math | reflexivity ].
    xsimpl*. }
  { xsimpl*. split; try math. destruct L; by rewrite ? Z.ltb_ge ? Z.ltb_lt. }
  { xsimpl*=> _ _. xwp; xapp. 
    replace (abs _) with (length L) by math. (* ... *)
    rewrite skipn_all List.app_nil_r /harray_fun lof_make_constfun; try math.
    replace (abs _) with (length L) by math. (* ... *) xsimpl*. }
Qed.

Definition alloc : val :=
  <{ fun 'n => 
      let 'p = val_alloc 'n in
      memset 'p; 
      'p }>.

Lemma htriple_alloc_unary {D : Type} `{Inhab D} (n : int) (d : D) :
  htriple (single d tt) (fun=> alloc n)
    \[0 <= n]
    (fun hv => \exists p, \[hv = fun=> val_loc p] \* harray_fun (fun=> a) p n d).
Proof with fold'.
  apply wp_equiv. xsimpl. intros HH.
  assert (n = abs n :> int) as E by math.
  rewrite -> E.
  xwp; xapp (@htriple_alloc_nat)=>x p EE... rewrite !EE.
  xwp; xapp (@htriple_memset_unary). xwp; xval. xsimpl*.
  rewrite -length_List_length length_make. xsimpl.
Qed.

End memset_alloc.

Section memset0_alloc0.

Definition memset0 := Eval unfold memset in memset 0.

Definition alloc0 := Eval unfold alloc in alloc 0.

Lemma htriple_alloc0_unary {D : Type} `{Inhab D} (n : int) (d : D) :
  htriple (single d tt) (fun=> alloc0 n)
    \[0 <= n]
    (fun hv => \exists p, \[hv = fun=> val_loc p] \* harray_fun_int (fun=> 0) p n d).
Proof.
  eapply htriple_conseq. 1: by apply htriple_alloc_unary. all: xsimpl*=>*.
  rewrite /harray_fun_int /harray_fun /harray_int !lof_indices map_conversion //.
Qed.

End memset0_alloc0.

Section memsetf0_allocf0.

Definition memsetf0 := Eval unfold memset in memset float_unit.

Definition allocf0 := Eval unfold alloc in alloc float_unit.

Lemma htriple_allocf0_unary {D : Type} `{Inhab D} (n : int) (d : D) :
  htriple (single d tt) (fun=> allocf0 n)
    \[0 <= n]
    (fun hv => \exists p, \[hv = fun=> val_loc p] \* harray_fun_float (fun=> float_unit) p n d).
Proof.
  eapply htriple_conseq. 1: by apply htriple_alloc_unary. all: xsimpl*=>*.
  rewrite /harray_fun_float /harray_fun /harray_float !lof_indices' map_conversion List.map_map //.
Qed.

End memsetf0_allocf0.
