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

Definition intlist_of_intfun (f : int -> int) (n : int) :
  @sigT (list int) (fun l =>
    (length l = abs n :> int /\ (forall i : int, 0 <= i < abs n -> nth (abs i) l 0 = f i))).
apply list_of_fun. math. Defined.

Fact lof_make_constfun (n c : int) (H : 0 <= n) :
  (projT1 (intlist_of_intfun (fun=> c) n)) = repeat c (abs n).
Proof.
  destruct (intlist_of_intfun _ _) as (l & Hlen & HH). simpl.
  apply nth_ext with (d:=0) (d':=0).
  1: rewrite repeat_length; math.
  intros i Hi. rewrite -> nth_indep with (l:=repeat _ _) (d':=c) by (rewrite repeat_length; math).
  rewrite -> nth_repeat, <- HH with (i:=i); try math.
  f_equal; math.
Qed.

End list_of_fun.

(* codomain restricted to be int; TODO make n int or nat here? *)
Definition harray_fun {D : Type} (f:int -> int) (p:loc) (n:int) (d : D) : hhprop D :=
  harray_int (projT1 (intlist_of_intfun f n)) p d.

Section alloc0.

Definition memset0 : val := Eval cbn zeta beta in
  let whilecond (i len : trm) := <{ let 'o = ! i in let 'c = 'o < len in 'c }> in
  let loopbody (p i : trm) := 
    <{ let 'o = ! i in
       val_array_set p 'o 0;
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
  (List.app (repeat (val_int 0) (abs (i+1))) (skipn (abs (i+1)) L)) =
  LibList.update (abs i) (val_int 0) (List.app (repeat (val_int 0) (abs i)) (skipn (abs i) L)).
Admitted.

(* TODO move this to somewhere else *)
Fact map_conversion [A B : Type] (l : list A) (f : A -> B) :
  LibList.map f l = map f l.
Proof.
  induction l; simpl; rewrite ?LibList.map_cons ?LibList.map_nil; auto; f_equal; auto.
Qed.

Lemma htriple_memset0_unary {D : Type} `{Inhab D} (L : list val) (p : loc) (d : D) :
  htriple (single d tt) (fun=> memset0 p)
    (harray L p d) 
    (fun=> harray_fun (fun=> 0) p (length L) d).
Proof with fold'.
  xwp; xapp (@htriple_array_length)...
  xwp; xapp=> s...
  remember (s d) as s0 eqn:Es0. (* ? *)
  xwp; xwhile1 0 (length L) (match L with nil => false | _ => true end)
    (fun (b : bool) (i : int) => \[i <= (length L) /\ Z.ltb i (length L) = b] \*
      s0 ~(d)~> i \* 
      harray (List.app (repeat (val_int 0) (abs i)) (skipn (abs i) L)) p d); try math.
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
    replace (harray _ p d)  (* TODO why simply rewriting does not work? *)
      with (harray (List.app (repeat (val_int 0) (abs (i+1))) (skipn (abs (i+1)) L)) p d) at 1.
    2: f_equal; now apply list_update_intermediate. 
    xapp IH; try math.
    1: split; [ math | reflexivity ].
    xsimpl*. }
  { xsimpl*. split; try math. destruct L; by rewrite ? Z.ltb_ge ? Z.ltb_lt. }
  { xsimpl*=> _ _. xwp; xapp. 
    replace (abs _) with (length L) by math. (* ... *)
    rewrite skipn_all List.app_nil_r /harray_fun /harray_int lof_make_constfun; try math.
    (* shall we abort LibList.map? *)
    rewrite map_conversion map_repeat. 
    replace (abs _) with (length L) by math. (* ... *) xsimpl*. }
Qed.

Definition alloc0 : val :=
  <{ fun 'n => 
      let 'p = val_alloc 'n in
      memset0 'p; 
      'p }>.

Lemma htriple_alloc0_unary {D : Type} `{Inhab D} (n : int) (d : D) (Hn : 0 <= n) :
  htriple (single d tt) (fun=> alloc0 n)
    \[]
    (fun hv => \exists p, \[hv d = val_loc p] \* harray_fun (fun=> 0) p n d).
Proof with fold'.
  assert (n = abs n :> int) as E by math.
  rewrite -> E.
  xwp; xapp (@htriple_alloc_nat)=>x p EE... rewrite !EE.
  xwp; xapp (@htriple_memset0_unary). xwp; xval. xsimpl*.
  rewrite -length_List_length length_make. xsimpl.
Qed.

End alloc0.