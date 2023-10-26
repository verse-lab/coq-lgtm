Set Implicit Arguments.
From SLF Require Import Fun LabType.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops Unary.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

(* some customized theory of from functions to lists *)
Lemma list_of_fun [A : Type] [def : A] (f : int -> A) (n : int) (H : 0 <= n) :
  @sigT (list A) (fun l =>
    (List.length l = n :> int /\ (forall i : int, 0 <= i < n -> List.nth (abs i) l def = f i))).
Proof.
  remember (abs n) as nn eqn:E.
  revert n H E. induction nn as [ | nn IH ]; intros.
  { assert (n = 0) as -> by math. exists (@nil A). split; auto. intros; math. }
  { assert (nn = abs (n - 1)) as Hq by math. apply IH in Hq; try math.
    destruct Hq as (la & H1 & H2). exists (List.app la (f (n - 1) :: nil)).
    rewrite -> List.app_length. split; simpl; try math.
    intros i Hin. destruct (Z.leb (n - 1) i) eqn:E2.
    { apply Z.leb_le in E2. replace i with (n-1) in * by math. 
      replace (abs (n-1)) with (List.length la) by math. now rewrite List.nth_middle. }
    { apply Z.leb_gt in E2. rewrite List.app_nth1. 1: apply H2. all: math. } }
Qed.

Definition intlist_of_intfun (f : int -> int) (n : int) :
  @sigT (list int) (fun l =>
    (List.length l = abs n :> int /\ (forall i : int, 0 <= i < abs n -> List.nth (abs i) l 0 = f i))).
apply list_of_fun. math. Defined.

(* codomain restricted to be int; TODO make n int or nat here? *)
Definition harray_fun {D : Type} (f:int -> int) (p:loc) (n:int) (d : D) : hhprop D :=
  harray_int (projT1 (intlist_of_intfun f n)) p d.

(* TODO possibly, some conversions between harray_int and harray_fun *)

Section alloc0.

Definition memset0 : val := Eval cbn zeta beta in
  let whilecond (i len : trm) := <{ let 'o = ! i in let 'c = 'o < len in 'c }> in
  let loopbody (p i : trm) := 
    <{ let 'o = ! i in
       let 'a = val_ptr_add p 1 in 
       let 'a = val_ptr_add 'a 'o in 
       'a := 0;
       ++ i }> in
  let loop := While (whilecond "i" "l") (loopbody "p" "i") in
  <{ fun 'p =>
      let 'l = val_length 'p in
      let 'i = ref 0 in 
      loop; 
      free 'i }>.

Ltac fold' := 
  rewrite ?wp_single
    -/(incr1.func _) 
    -/(While_aux _ _) 
    -/(While _ _) //=.
(*
Lemma htriple_memset0_unary {D : Type} `{Inhab D} (L : list val) (p : loc) (d : D) :
  htriple (single d tt) (fun=> memset0 p)
    (harray L p d) 
    (fun=> harray_fun (fun=> 0) p (List.length L) d).
Proof with fold'.
  xwp; xapp (@htriple_array_length)...
  xwp; xapp=> s.
*)
End alloc0.
