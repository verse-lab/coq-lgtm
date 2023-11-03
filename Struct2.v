Set Implicit Arguments.
From SLF Require Import Fun LabType ListCommon.
From SLF Require Import LibWP LibSepSimpl LibSepReference LibSepTLCbuffer Struct Loops Unary.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Definition harray_fun {D : Type} (f:int -> val) (p:loc) (n:int) (d : D) : hhprop D :=
  harray (projT1 (list_of_fun' f n)) p d.

Definition harray_fun_int {D : Type} (f:int -> int) (p:loc) (n:int) (d : D) : hhprop D :=
  harray_int (lof f n) p d.

Definition harray_fun_float {D : Type} (f:int -> binary64) (p:loc) (n:int) (d : D) : hhprop D :=
  harray_float (projT1 (list_of_fun' f n)) p d.

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
  rewrite /harray_fun_int /harray_fun /harray_int !(lof_indices val_uninit) map_conversion //.
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
  rewrite /harray_fun_float /harray_fun /harray_float (lof_indices' val_uninit) (lof_indices' float_unit) map_conversion List.map_map //.
Qed.

End memsetf0_allocf0.

(* TODO do not know where to put these; temporarily here *)
Definition feq_val (v1 v2 : val) :=
  match v1, v2 with val_float f1, val_float f2 => @feq Tdouble f1 f2 | _, _ => v1 = v2 end.

Global Instance feq_val_eqrel : RelationClasses.Equivalence feq_val.
Proof.
  constructor; hnf. 1: intros []=> //=. 1: intros [] []=> /= ? //=; by symmetry.
  intros [] []=> //; intros [] => //. all: unfold feq_val; intros HH1; by rewrite HH1.
Qed.
