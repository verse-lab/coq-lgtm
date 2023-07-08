Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct.
From SLF Require Import Fun LabType.
From mathcomp Require Import ssreflect ssrfun.
Hint Rewrite conseq_cons' : rew_listx.

Module NatDom : Domain with Definition type := nat.
Definition type := nat.
End NatDom.

Module IntDom : Domain with Definition type := int.
Definition type := int.
End IntDom.

(* Module ArrayDemo (Dom : Domain). *)

Module Export AD := WithArray(IntDom).
Check eq_refl : D = labeled int.

Global Instance Inhab_D : Inhab D. 
Proof Build_Inhab (ex_intro (fun=> True) (Lab (0, 0) 0) I).

Section Demo.

(* assume properties about the running-length encoding. *)
(*
Variables (N M : nat) (Lval : list int) (Lind : list nat).
Hypothesis H_length_Lval : length Lval = M.
Hypothesis H_length_Lind : length Lind = S M.
Hypothesis H_Lind_first : nth 0%nat Lind = 0%nat.
Hypothesis H_Lind_last : nth M Lind = N.
Hypothesis H_Lind_inc : forall (i j : nat), 0%nat <= i < M -> 0%nat <= j <= M -> 
  (i < j)%nat -> nth i Lind < nth j Lind.
Hypothesis H_Lval_notnil : (1 <= M)%nat.
*)

(* should not mix notations on nat and Z ... *)

Variables (N M : int) (Lval : list int) (Lind : list int).
Hypothesis H_length_Lval : length Lval = abs M.
Hypothesis H_length_Lind : length Lind = abs (M + 1).
Hypothesis H_Lind_first : nth 0%nat Lind = 0.
Hypothesis H_Lind_last : nth (abs M) Lind = N.
Hypothesis H_Lind_inc : forall (i j : nat), 
  (0 <= (nat_to_Z i) <= abs M)%Z -> 
  (0 <= (nat_to_Z j) <= abs M)%Z -> 
  (i < j)%nat -> 
  (nth i Lind < nth j Lind)%Z.
Hypothesis H_Lval_notnil : (0 < M)%Z.

Fact H_Lind_inc' : forall (i j : int), 
  (0 <= i <= M)%Z -> 
  (0 <= j <= M)%Z -> 
  (i <= j)%Z -> 
  (nth (abs i) Lind <= nth (abs j) Lind)%Z.
Proof using M Lind H_Lind_inc.
  clear N Lval H_length_Lval H_length_Lind H_Lval_notnil H_Lind_last H_Lind_first.

  intros. destruct (Z.eqb i j) eqn:E.
  { rewrite -> Z.eqb_eq in E. subst i. reflexivity. }
  { rewrite -> Z.eqb_neq in E. assert (i < j)%Z by math.
    match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end. 
    apply H_Lind_inc; math.
  }
Qed. 

Definition rlsum_loopbody (real_x_ind real_x_val real_s : trm) :=
  (* need to make it a term; otherwise subst cannot penetrate *)
  <{ fun_ "i" => 
      let "tmp1" = ! real_s in
      let "tmp2" = val_array_get real_x_val "i" in
      let "tmp3" = "i" + 1 in
      let "tmp4" = val_array_get real_x_ind "tmp3" in
      let "tmp5" = val_array_get real_x_ind "i" in
      let "tmp6" = "tmp4" - "tmp5" in
      let "tmp7" = "tmp2" * "tmp6" in
      let "tmp8" = "tmp1" + "tmp7" in
      real_s := "tmp8" }>.

  (* trm_fun "i"
  (val_set real_s
     (val_get
        (val_add real_s
           (val_mul (val_array_get real_x_val "i")
              (val_sub (val_array_get real_x_ind (val_add "i" 1))
                 (val_array_get real_x_ind "i")))))). *)

Definition rlsum_func :=
  let loopbody := rlsum_loopbody "x_ind" "x_val" "s" in
  let loop := For 0 M loopbody in
  (* the arguments should be the location of arrays? *)
  <{ fun "x_ind" "x_val" => 
      let "s" = ref 0 in 
      loop ; 
      ! "s"
  }>.

Definition rli_whilecond (i : int) (real_x_ind real_j : trm) :=
  (* intermediate lang *)
  (* (<{ (val_array_get real_x_ind (! (real_j + 1))) <= i }>). *)
  (<{ let "tmp1" = ! real_j in
      let "tmp2" = "tmp1" + 1 in
      let "tmp3" = val_array_get real_x_ind "tmp2" in
      "tmp3" <= i }>).

Definition rli_whilebody (real_j : trm) :=
  (* or incr j? *)
  (* (<{ real_j := (! real_j) + 1 }>). *)
  (<{ let "tmp1" = ! real_j in
      let "tmp2" = "tmp1" + 1 in
      real_j := "tmp2" }>).

Definition rli_func (i : int) :=
  let loop := While (rli_whilecond i "x_ind" "j")
    (rli_whilebody "j") in
  <{ fun "x_ind" "x_val" => 
      let "j" = ref 0 in 
      loop ; 
      (let "tmp" = ! "j" in (val_array_get "x_val" "tmp"))
  }>.

Definition arr_x_ind (p : loc) (d : D) :=
  (* harray (LibList.map (fun n => val_int (Z.of_nat n)) Lind) p d. *)
  harray (LibList.map val_int Lind) p d.

Definition arr_x_val (p : loc) (d : D) :=
  harray (LibList.map val_int Lval) p d.

(* sums are equal *)

Fact For_subst ZZ NN t x v : 
  x <> "cond" -> 
  x <> "for" ->
  x <> "cnt" -> 
  x <> "body" ->
  subst x v (For ZZ NN t) = For ZZ NN (subst x v t).
Proof using.
  intros. unfold For, For_aux. simpl; case_var; eqsolve.
Qed.

Definition val_int_add (a b : val) :=
  (match a with val_int a' => a' | _ => 0 end) + 
    (match b with val_int a' => a' | _ => 0 end).

Fact comm_val_int_add : comm val_int_add.
Proof using. 
  clear.
  hnf. intros. unfold val_int_add. destruct x, y; try math; auto.
Qed.

Fact assoc_val_int_add : assoc val_int_add.
Proof using. 
  clear.
  hnf. intros. unfold val_int_add. destruct x, y, z; try math; auto.
Qed.

(* Definition int_add_val_int (b : int) (a : val) :=
  b + (match a with val_int a' => a' | _ => 0 end). *)

(*
(* a subgoal for goal and other programs *)
Goal forall (px_ind px_val : loc) (ps0 : loc),
  ntriple 
    (ps0 ~⟨(1%Z, 0%Z), 0⟩~> 0 \*
      arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
      arr_x_val px_val (⟨(1, 0), 0⟩)%arr \*
      (\*_(d <- interval 0 N)
          arr_x_ind px_ind (⟨(2, 0), d⟩)%arr \*
          arr_x_val px_val (⟨(2, 0), d⟩)%arr))
    ((Lab (pair 1 0) (FH (single 0 tt) (fun=> 
      For 0 M (rlsum_loopbody (val_loc px_ind) (val_loc px_val) (val_loc ps0))
      ))) :: 
      (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => (fun hveta => ps0 ~⟨(1%Z, 0%Z), 0⟩~> 
      (fset_fold 0 (fun d acc => int_add_val_int acc (hveta d)) 
        (label (Lab (pair 2 0) (interval 0 N)))) \* \Top) hv).
Proof.
  intros.
  unfold rlsum_loopbody.
  eapply xfor_lemma.




*)

Definition ind_seg (i : int) := 
  (* interval (Z.of_nat (nth (Z.to_nat i) Lind)) (Z.of_nat (nth (Z.to_nat (i + 1)) Lind)). *)
  interval (nth (abs i) Lind) (nth (abs (i + 1)) Lind).

Lemma interval_segmentation_pre i :
  0 <= i <= M -> 
  Union (interval 0 i) ind_seg = interval 0 (nth (abs i) Lind).
Proof using N M Lind H_length_Lind H_Lind_first H_Lind_inc.
  clear Lval H_length_Lval H_Lind_last H_Lval_notnil.

  remember (to_nat i) as n.
  revert i Heqn.
  induction n as [ | n IH ]; intros.
  { assert (i = 0) as -> by math. 
    replace (abs 0) with O by math. 
    rewrite -> H_Lind_first. simpl. rewrite -> intervalgt; try math.
    by rewrite -> Union0.
  }
  { assert (i = (nat_to_Z n) + 1) as -> by math.
    rewrite -> intervalUr; try math.
    rewrite -> Union_upd_fset, -> IH; try math.
    unfold ind_seg. 
    replace ((abs n)) with n by math.
    replace (abs (n + 1)) with (S n) by math.
    rewrite <- interval_union with (x:=0) (y:=(nth n Lind))
      (z:=(nth (S n) Lind)); try math.
    2:{
      rewrite <- H_Lind_first. 
      destruct n; try math. 
      match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end. 
      apply H_Lind_inc; math. 
    }
    2:{ match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end. 
      apply H_Lind_inc; math. 
    }
    rewrite -> union_comm_of_disjoint. 1: reflexivity.
    (* TODO may reuse disjoint proof *)
    apply disjoint_of_not_indom_both.
    intros. rewrite -> indom_interval in *. math.
  }
Qed.

Lemma interval_segmentation :
  Union (interval 0 M) ind_seg = interval 0 N.
Proof using N M Lind H_length_Lind H_Lind_first H_Lind_inc H_Lind_last H_Lval_notnil.
  clear Lval H_length_Lval.

  rewrite -> interval_segmentation_pre with (i:=M). 2: math.
  rewrite <- H_Lind_last.
  f_equal.
Qed.

(* order property of this array *)
(* Lemma ind_find_unique : forall (k : int)
  (Hk : (0 <= k < N)%Z) (a : int) (Ha : (0 <= a < M)%Z) 
  (Hka : (nth (abs a) Lind <= k < nth (abs (a + 1)) Lind)%Z),  *)

(*
Lemma interval_segmentation_pre i :
  0 <= i <= M -> 
  Union (interval 0 i) ind_seg = interval 0 (Z.of_nat (nth (Z.to_nat i) Lind)).
Proof using N M Lind H_length_Lind H_Lind_first H_Lind_inc.
  clear Lval H_length_Lval H_Lind_last H_Lval_notnil.

  remember (to_nat i) as n.
  revert i Heqn.
  induction n as [ | n IH ]; intros.
  { assert (i = 0) as -> by math. 
    rewrite -> H_Lind_first. simpl. rewrite -> intervalgt; try math.
    by rewrite -> Union0.
  }
  { assert (i = (Z.of_nat n) + 1) as -> by math.
    rewrite -> intervalUr; try math.
    rewrite -> Union_upd_fset, -> IH; try math.
    unfold ind_seg. 
    replace (to_nat (Z.of_nat n)) with n by math.
    replace (to_nat (Z.of_nat n + 1)) with (S n) by math.
    rewrite <- interval_union with (x:=0) (y:=(Z.of_nat (nth n Lind)))
      (z:=(Z.of_nat (nth (S n) Lind))); try math.
    2:{ apply inj_le, H_Lind_inc; math. }
    rewrite -> union_comm_of_disjoint. 1: reflexivity.
    (* TODO may reuse disjoint proof *)
    apply disjoint_of_not_indom_both.
    intros. rewrite -> indom_interval in *. math.
  }
Qed.

Lemma interval_segmentation :
  Union (interval 0 M) ind_seg = interval 0 N.
Proof using N M Lind H_length_Lind H_Lind_first H_Lind_inc H_Lind_last.
  clear Lval H_length_Lval H_Lval_notnil.

  rewrite -> interval_segmentation_pre with (i:=M). 2: math.
  rewrite <- H_Lind_last.
  f_equal. replace (to_nat M) with M by math. math.
Qed.
*)

Fact UnionN0 [T D S : Type] (fs : fset T) : Union fs (fun=> @empty D S) = empty.
Proof using.
  pattern fs. apply fset_ind; clear fs.
  { by rewrite -> Union0. }
  { intros. rewrite -> Union_upd. 2: auto. by rewrite -> H, -> union_empty_l. }
Qed.

Lemma hbig_fset_label_single' (Q : D -> hhprop) (d : D) :
  \*_(d0 <- single d tt) Q d0 = Q d.
Proof using.
  unfold hbig_fset.
  rewrite -> update_empty. rewrite -> (snd (@fset_foldE _ _ _ _)); auto.
  2: intros; xsimpl.
  rewrite -> (fst (@fset_foldE _ _ _ _)); auto.
  by rewrite -> hstar_hempty_r.
Qed.

(* sub-part: evaluating while condition *)
Lemma rli_whilecond_spec : forall (j k : int) (pj0 px_ind : loc) (d : D)
  (Hj : (0 <= j < M)%Z),
  (pj0 ~(d)~> j \* arr_x_ind px_ind d) ==>
  wp (single d tt) (fun=> rli_whilecond k px_ind pj0) 
    (fun hv => \[hv d = (Z.leb (nth (abs (j+1)) Lind) k)] \* pj0 ~(d)~> j \* arr_x_ind px_ind d).
Proof.
  intros.
  xwp. xlet.
  (* hard to only wp *)
  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> j).
  1:{
    replace (pj0 ~(d)~> j) with (\*_(d0 <- single d tt) (pj0 ~(d0)~> j)).
    2: apply hbig_fset_label_single'.
    apply htriple_get.
  }
  1: apply himpl_refl.
  xsimpl.
  intros ? ->.
  xwp. xlet. xapp.
  xwp. xlet.
  (* use array opr triple *)
  apply wp_equiv.

  (* again? *)
  eapply htriple_conseq_frame with (H1:=arr_x_ind px_ind d).
  1:{ 
    replace (arr_x_ind px_ind d) with 
      (\*_(d0 <- single d tt) (arr_x_ind px_ind d0)).
    2: apply hbig_fset_label_single'.
    apply htriple_array_get.
    { intros. rewrite -> length_map, -> H_length_Lind. math. }
    { intros. reflexivity. } 
  }
  1: xsimpl.
  xsimpl.
  introv Er. specialize (Er d (indom_single _ _)).

  apply wp_equiv.
  eapply htriple_conseq_frame with (H1:=\[]).
  1:{
    apply wp_equiv. 
    rewrite -> wp_ht_eq with (ht2:=fun=> trm_app (trm_app val_le (r d)) k).
    2:{
      introv H. rewrite -> indom_single_eq in H. by subst.
    }
    (* bad *)
    apply wp_equiv, htriple_binop.
    introv H. 
    instantiate (1:=fun=> (Z.leb (nth (abs (j+1)) Lind) k)). simpl.
    rewrite -> Er.
    pose proof (evalbinop_le (nth (abs (j+1)) Lind) k) as HH.
    rewrite -> nth_map. 2: math.
    rewrite -> isTrue_eq_if in HH.
    case_if. 
    { assert (nth (abs (j + 1)) Lind <=? k = true)%Z as ->; auto.
      apply Z.leb_le. math.
    }
    { assert (nth (abs (j + 1)) Lind <=? k = false)%Z as ->; auto.
      apply Z.leb_gt. math.
    }
  }
  1: rewrite -> hstar_hempty_l; apply himpl_refl.
  xsimpl. 1: intros ? ->; reflexivity.
  intros ? ->.
  rewrite -> ! hbig_fset_label_single'.
  xsimpl.
Qed.

Lemma rli_whilebody_spec : forall (pj0 : loc) (d : D) (j : int),
  (pj0 ~(d)~> j) ==>
  wp (single d tt) (fun=> rli_whilebody pj0) 
    (fun=> pj0 ~(d)~> (j+1)).
Proof using.
  intros.
  unfold rli_whilebody.
  xwp. xlet.
  apply wp_equiv.
  eapply htriple_conseq_frame with (H2:=\[]).
  2: xsimpl.
  1:{ 
    rewrite <- hbig_fset_label_single' with (Q:=fun d0 => pj0 ~(d0)~> j).
    apply htriple_get.
  }
  xsimpl.
  intros ? ->.
  xwp. xlet. xapp. xapp. by rewrite -> hbig_fset_label_single'.
Qed.

(* using While on a single program *)
Lemma rli_func_spec : forall (d : D) (px_ind px_val : loc) (k : int)
  (Hk : (0 <= k < N)%Z) (a : int) (Ha : (0 <= a < M)%Z) 
  (Hka : (nth (abs a) Lind <= k < nth (abs (a + 1)) Lind)%Z), 
  htriple (single d tt) 
    (fun=> rli_func k px_ind px_val)
    (arr_x_ind px_ind d \* arr_x_val px_val d)
    (fun hv => \[hv d = val_int (nth (abs a) Lval)] \* arr_x_ind px_ind d \* arr_x_val px_val d \* \Top).
Proof.
  intros. 
  unfold rli_func.
  (* do app2 for rlsum *)
  eapply htriple_eval_like.
  1: apply eval_like_app_fun2; eqsolve.
  (* subst pushdown *)
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  (* assign location *)

  eapply htriple_let.
  1:{ 
    rewrite <- hstar_hempty_l at 1.
    eapply htriple_frame. apply htriple_ref.
  }
  intros. simpl. 
  (* simplify hexists *)
  apply wp_equiv.
  xsimpl. intros pj ->. xsimpl.
  (* use only one point location of pj; then forget pj *)
  remember (pj d) as pj0.
  erewrite -> wp_ht_eq with (ht2:=
    fun=> trm_seq (While (rli_whilecond k px_ind pj0) (rli_whilebody pj0)) 
      (trm_let "tmp" (val_get pj0) (val_array_get px_val "tmp"))).
  2:{ 
    intros. unfolds While, While_aux, rli_whilecond, rli_whilebody. 
    rewrite -> indom_single_eq in H. by subst.
  }
  apply wp_equiv.
  eapply htriple_conseq.
  3: apply qimpl_refl.
  2:{
    apply himpl_frame_l with (H1':=pj0 ~(d)~> 0). subst pj0.
    rewrite -> update_empty, -> hbig_fset_update, -> hbig_fset_empty; auto.
    xsimpl.
  }
  clear pj Heqpj0.
  (* use single wp_while here *)
  apply wp_equiv.
  xwp. xseq.
  apply wp_equiv.

  (* first have to check if a = 0 or not; slightly troublesome here *)
  remember (abs a) as n eqn:E.
  destruct n as [ | n ].
  1:{
    replace a with 0 in * by math.
    replace (0+1) with 1 in * by math.
    replace (abs 1) with 1%nat in Hka by math.

    unfold While, While_aux, rli_whilecond.
    apply wp_equiv. rewrite -> wp_fix_app2. 
    apply wp_equiv, htriple_app_fix_direct.
    simpl.
    apply wp_equiv.    
    xwp. xlet.

    (* use the spec above *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> 0 \* arr_x_ind px_ind d).
    2: xsimpl.
    1:{ apply wp_equiv, rli_whilecond_spec. math. }
    xsimpl.
    intros r Er.
    change (abs (0 + 1)) with 1%nat in Er.

    (* ready for the rest *)
    match goal with |- himpl _ (wp _ ?ht _) => pose (ff:=ht) end.
    erewrite -> wp_ht_eq with (ht2:=fun=> ff d).
    2:{ 
      intros. rewrite -> indom_single_eq in H. by subst.
    }
    subst ff. simpl.
    destruct Hka as (_ & Hka).
    rewrite <- Z.leb_gt in Hka.
    rewrite -> Hka in Er.
    xwp. rewrite -> Er. xif. 1: intros; by false.
    intros _. 
    xwp. xval. 
    xwp. xlet.
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> 0).
    1:{
      replace (pj0 ~(d)~> 0) with (\*_(d0 <- single d tt) (pj0 ~(d0)~> 0)).
      2: apply hbig_fset_label_single'.
      apply htriple_get.
    }
    1: apply himpl_refl.
    xsimpl.
    intros ? ->.

    (* restore the thing array get after seq *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=arr_x_val px_val d).
    1:{ 
      replace (arr_x_val px_val d) with 
        (\*_(d0 <- single d tt) (arr_x_val px_val d0)).
      2: apply hbig_fset_label_single'.
      apply htriple_array_get.
      { intros. rewrite -> length_map, -> H_length_Lval. math. }
      { intros. reflexivity. } 
    }
    1: xsimpl.
    xsimpl.
    { 
      introv Er0. specialize (Er0 d (indom_single _ _)).
      rewrite -> Er0, -> nth_map; math.
    }
    {
      introv Er0. specialize (Er0 d (indom_single _ _)).
      rewrite -> ! hbig_fset_label_single'.
      xsimpl.
    }
  }

  assert (0 < a < M)%Z as (Ha1 & Ha2) by math.
  rewrite -> E in Hka.
  (* use single wp_while here *)
  rewrite <- union_empty_r with (h:=single d tt).
  apply wp_equiv.
  eapply wp_while with (fsi:=fun=> empty) (s:=d) (Z:=0) (N:=a) (b0:=true) (hv0:=fun=> val_unit)
    (Inv:=fun b j _ => \[(0 <= j < M)%Z /\
      (nth (abs j) Lind <= k)%Z /\ b = Z.leb (nth (abs (j+1)) Lind) k] 
      \* pj0 ~(d)~> j \* arr_x_ind px_ind d \* arr_x_val px_val d)
    (HC:=fun c b j _ => \[(0 <= j < M)%Z /\ c = b /\ 
      (nth (abs j) Lind <= k)%Z /\ b = Z.leb (nth (abs (j+1)) Lind) k] 
      \* pj0 ~(d)~> j \* arr_x_ind px_ind d \* arr_x_val px_val d).
  17: reflexivity.
  9-15: auto; try math.
  8: by rewrite -> UnionN0.
  7: math.
  7: intros; auto.
  { intros b j _. xsimpl. intros (H1 & H2 & ->).
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> j \* arr_x_ind px_ind d).
    1:{ apply wp_equiv, rli_whilecond_spec. math. }
    1: xsimpl.
    xsimpl.
    { intros. rewrite H. reflexivity. }
    { intros. auto. }
  }
  { intros b j _. xsimpl.
    { intros (Hj & <- & Hleb & EE).
      symmetry in EE.
      split; auto.
      (* here is the unique proof *)
      rewrite -> Z.leb_gt in EE.
      destruct Hka as (Hka1 & Hka2).
      destruct (Z.leb (j+1) a) eqn:Eu.
      { rewrite -> Z.leb_le in Eu.
        enough (nth (abs (j + 1)) Lind <= nth (abs a) Lind)%Z by math.
        apply H_Lind_inc'; math.
      }
      { destruct (Z.leb (a+1) j) eqn:Eu'.
        { rewrite -> Z.leb_le in Eu'.
          enough (nth (abs (a + 1)) Lind <= nth (abs j) Lind)%Z by math.
          apply H_Lind_inc'; math.
        }
        { rewrite -> Z.leb_gt in Eu, Eu'. math. }
      }
    }
    { intros (Hj & <- & Hleb & EE).
      split; auto.
    }
  }
  { intros b j hv (Hj1 & Hj2) IH.
    xsimpl. intros (_ & <- & H1 & H2).
    symmetry in H2. rewrite -> Z.leb_le in H2.
    rewrite -> UnionN0, -> union_empty_r.
    rewrite -> wp_ht_eq with (ht2:=fun=> trm_seq (rli_whilebody pj0) 
       (While (rli_whilecond k px_ind pj0) (rli_whilebody pj0))).
    2:{ 
      introv HH. unfold upd. 
      rewrite -> indom_single_eq in HH. subst. case_if; eqsolve.
    }
    xwp. xseq.

    (* body: a simple incr *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> j).
    2: xsimpl.
    1: apply wp_equiv; apply rli_whilebody_spec.
    xsimpl.

    destruct (Z.leb (a-1) j) eqn:Ef.
    { (* check if it is the end *)
      rewrite -> Z.leb_le in Ef.
      assert (j = a - 1) as -> by math.
      replace (a - 1 + 1) with a in * by math.
      
      (* script reuse *)
      unfold While, While_aux, rli_whilecond.
      rewrite -> wp_fix_app2. 
      apply wp_equiv, htriple_app_fix_direct.
      simpl.
      apply wp_equiv.    
      xwp. xlet.

      (* use the spec above *)
      apply wp_equiv.
      eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> a \* arr_x_ind px_ind d).
      2: xsimpl.
      1:{ apply wp_equiv, rli_whilecond_spec. math. }
      xsimpl.
      intros r Er.

      (* ready for the rest *)
      match goal with |- himpl _ (wp _ ?ht _) => pose (ff:=ht) end.
      erewrite -> wp_ht_eq with (ht2:=fun=> ff d).
      2:{ 
        intros. rewrite -> indom_single_eq in H. by subst.
      }
      subst ff. simpl.
      destruct Hka as (_ & Hka).
      rewrite <- Z.leb_gt in Hka.
      rewrite -> Hka in Er.
      xwp. rewrite -> Er. xif. 1: intros; by false.
      intros _. 
      xwp. xval.

      xsimpl. split; auto. eqsolve.
    }
    { (* use IH *)
      rewrite -> Z.leb_gt in Ef. clear Hj2.
      assert (j + 1 < a)%Z as Hj2 by math.
      assert (j < j + 1)%Z as Hj3 by math.
      specialize (IH (j+1) true (fun=> val_unit) (conj Hj3 Hj2)).
      rewrite -> UnionN0, -> union_empty_r in IH.
      rewrite -> wp_ht_eq with (ht2:=fun=> 
        (While (rli_whilecond k px_ind pj0) (rli_whilebody pj0))) in IH.
      2:{ 
        introv HH. unfold upd. 
        rewrite -> indom_single_eq in HH. subst. case_if; eqsolve.
      }
      apply wp_equiv.
      destruct Hka as (Hka1 & Hka2).
      eapply htriple_conseq.
      1: apply wp_equiv, IH.
      { xsimpl. split; try math. split; try assumption. 
        symmetry. apply Z.leb_le.
        transitivity (nth (abs a) Lind); try assumption. 
        destruct (Z.leb a (j+1+1)) eqn:EE.
        { rewrite -> Z.leb_le in EE.
          assert (j+1+1 = a) as -> by math.
          reflexivity.
        }
        { rewrite -> Z.leb_gt in EE.
          match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end.
          apply H_Lind_inc; math.
        }
      }
      auto.
    }
  }
  { intros. auto. }
  { xsimpl. split; try math. destruct Hka as (Hka1 & Hka2). split.
    { transitivity (nth (abs a) Lind); try assumption.
      match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end.
      apply H_Lind_inc; math.
    }
    { symmetry. apply Z.leb_le. change (0+1) with 1.
      transitivity (nth (abs a) Lind); try assumption.
      destruct n. 1: replace a with 1 by math; reflexivity.
      match goal with |- (?a <= ?b)%Z => enough (a < b)%Z; try math end.
      apply H_Lind_inc; math.
    }
  }
  { xsimpl. intros _ (_ & H1 & H2).
    symmetry in H2. rewrite -> Z.leb_gt in H2.
    rewrite -> E, -> union_empty_r.

    (* again the rest part? *)
    xwp. xlet.
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=pj0 ~(d)~> a).
    1:{
      replace (pj0 ~(d)~> a) with (\*_(d0 <- single d tt) (pj0 ~(d0)~> a)).
      2: apply hbig_fset_label_single'.
      apply htriple_get.
    }
    1: apply himpl_refl.
    xsimpl.
    intros ? ->.

    (* restore the thing array get after seq *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=arr_x_val px_val d).
    1:{ 
      replace (arr_x_val px_val d) with 
        (\*_(d0 <- single d tt) (arr_x_val px_val d0)).
      2: apply hbig_fset_label_single'.
      apply htriple_array_get.
      { intros. rewrite -> length_map, -> H_length_Lval. math. }
      { intros. reflexivity. } 
    }
    1: xsimpl.
    xsimpl.
    { 
      introv Er0. specialize (Er0 d (indom_single _ _)).
      rewrite -> Er0, -> nth_map; math.
    }
    {
      introv Er0. specialize (Er0 d (indom_single _ _)).
      rewrite -> ! hbig_fset_label_single'.
      xsimpl.
    }
  }
Qed.
(*
Lemma htriple_hmerge_frame fs ht P Q p d (v diff : int) : 
  (forall (v diff : int), 
    htriple fs ht (hsingle p d v) 
      (fun=> hstar (hsingle p d (v + diff)) (hpure P))) ->
  htriple fs ht 
    (hmerge val_int_add Q (hsingle p d v))
    (fun=> hstar (hmerge val_int_add Q (hsingle p d (v + diff))) (hpure P)).
Proof.
  intros H.
  unfold htriple in H |- *. intros H'.
  unfold hhoare in H |- *. intros h Hh.
  unfold hmerge in Hh. apply hstar_inv in Hh.
  destruct Hh as (hm & hh' & (hq & hs & Hq & Hs & Em) & Hh' & Hdj & E).
  apply hsingle_inv in Hs.
  subst h hs. 

  destruct (fmap_data hm (p, d)) eqn:E.
  2:{ 
    subst hm. unfold Fmap.merge, Fmap.map_merge in E. simpl in E.
    case_if.
    by destruct (fmap_data hq (p, d)) eqn:E'.
  }
  assert (exists delta, v0 = val_int (v + delta)).
  {
    subst hm. unfold Fmap.merge, Fmap.map_merge in E. simpl in E.
    case_if.
    destruct (fmap_data hq (p, d)) eqn:E'.
    { destruct (match v1 with val_int _ => true | _ => false end) eqn:E2.
      { destruct v1; try eqsolve.
        unfold val_int_add in E. injection E as <-.
        exists z. math.
      }
      { destruct v1; try eqsolve.
        all: unfold val_int_add in E; injection E as <-.
        all: exists 0; math.
      }
    }
    injection E as <-.
    exists 0; math.
  }
  destruct H0 as (delta & ->).
  
  specialize (H (v + delta) diff H'
    (Fmap.union (Fmap.single (p, d) (val_int (v + delta))) hh')).
  match type of H with ?a -> _ => assert a as Hhead end.
  { apply hstar_intro; try assumption.
    1: apply hsingle_intro.
    apply disjoint_of_not_indom_both.
    intros. 
    assert (indom hm x) as Htmp.
    { subst hm. rewrite -> indom_merge_eq. right.
      by rewrite -> indom_single_eq in H0 |- *.
    }
    revert Htmp H1. by apply disjoint_inv_not_indom_both.
  }
  specialize (H Hhead). clear Hhead.

  destruct H as (h'' & hv & H & Hh'').
  pose proof (@Fmap.remove_update_self _ _ _ _ _ E) as Hself.
  rewrite -> update_eq_union_single in Hself.
Abort.
*)

(*
Lemma hmerge_split Q p d :
  let Q' := fun h => 
  forall v : int, hmerge val_int_add Q (hsingle p d v) ==>
    hexists (fun diff : int =>
      hstar Q' (hsingle p d (val_int_add v (val_int diff)))).
Proof.

Lemma hmerge_split Q p d :
  forall v : int, hmerge val_int_add Q (hsingle p d v) ==>
    hexists (fun Q' => hexists (fun diff : int =>
      hstar Q' (hsingle p d (val_int_add v (val_int diff))))).
Proof.
  intros.
  hnf. intros h Hh.
  unfold hmerge in Hh. destruct Hh as (h1 & h2 & H1 & H2 & E).
  apply hsingle_inv in H2.
  (* now ask *)
  destruct (fmap_data h1 (p, d)) eqn:E1.
  { destruct (match v0 with val_int _ => true | _ => false end) eqn:E2.
    { destruct v0; try eqsolve.

      

  hexists_intro
  
*)  

Lemma rlsum_rli_align_step : forall (px_ind px_val : loc) (ps0 : loc),
  ntriple 
    (ps0 ~⟨(1%Z, 0%Z), 0⟩~> 0 \*
      arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
      arr_x_val px_val (⟨(1, 0), 0⟩)%arr \*
      (\*_(d <- interval 0 N)
          arr_x_ind px_ind (⟨(2, 0), d⟩)%arr \*
          arr_x_val px_val (⟨(2, 0), d⟩)%arr))
    ((Lab (pair 1 0) 
        (FH (single 0 tt) (fun=> 
          For 0 M (rlsum_loopbody (val_loc px_ind) (val_loc px_val) (val_loc ps0))
          ))) :: 
      (Lab (pair 2 0) 
        (FH (Union (interval 0 M) ind_seg) 
          (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => (fun hveta => ps0 ~⟨(1%Z, 0%Z), 0⟩~> 
      (fset_fold (val_int 0) 
        (* (fun d acc => int_add_val_int acc (hveta d)) *)
        (fun d acc => val_int_add acc (hveta d))
        (label (Lab (pair 2 0) (interval 0 N)))) \* \Top) hv).
Proof.
  intros.
  unfold rlsum_loopbody.
  eapply xfor_lemma with (m:=val_int_add)
    (Inv:=fun=> arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
      arr_x_val px_val (⟨(1, 0), 0⟩)%arr)
    (R:=fun j => 
      (arr_x_ind px_ind (Lab (2, 0) j) \* arr_x_val px_val (Lab (2, 0) j)))
    (R':=fun j => 
      (arr_x_ind px_ind (Lab (2, 0) j) \* arr_x_val px_val (Lab (2, 0) j)))
    (H:=fun=> ps0 ~⟨(1%Z, 0%Z), 0⟩~> 0)
    (H':=fun i hv => ps0 ~⟨(1%Z, 0%Z), 0⟩~> 
      (fset_fold (val_int 0) 
        (fun d acc => val_int_add acc (hv d))
        (label (Lab (pair 2 0) (ind_seg i))))).
  all: match goal with |- context[subst _ _ _ = _] => intros; auto | _ => idtac end.
  all: match goal with |- context[var_eq ?a ?b] => intros; auto | _ => idtac end.
  10-11: math.
  8: apply comm_val_int_add.
  8: apply assoc_val_int_add.
  7:{
    intros. erewrite -> fold_fset_eq. 1: reflexivity.
    simpl. intros (l, d) HH.
    rewrite -> indom_label_eq in HH.
    destruct HH as (<- & HH). specialize (H _ HH).
    extens. intros. f_equal. by f_equal. (* ? *)
  }
  (* important *)
  (* pre *)
  7:{
    rewrite <- interval_segmentation.
    xsimpl.
    admit.
  }
  (* post *)
  7:{
    intros. xsimpl.
    rewrite -> hstars_pick_last_4. 
    eapply himpl_trans.
    1: apply himpl_frame_l.
    2: apply himpl_frame_r; xsimpl.
    admit.
  }
  (* main *)
  1:{
    intros l Q (Hl1 & Hl2).
    apply (xfocus_lemma (pair 2 0)); simpl; try apply xnwp0_lemma.
    rewrite -> union_empty_r.

    (* little change *)
    rewrite -> wp_ht_eq with (ht2:=(fun d => ((rli_func (eld d)) px_ind px_val))).
    2:{ intros. unfolds label. 
      rewrite -> indom_Union in H. 
      setoid_rewrite -> indom_single_eq in H.
      simpl in H.
      destruct H as (? & H & <-).
      simpl. case_if; eqsolve.
    }
    
    (* bundle *)
    apply wp_equiv.
    eapply htriple_conseq_frame with (H1:=(\*_(d <- (label (Lab (2, 0) (ind_seg l))))
      arr_x_ind px_ind (Lab (2, 0) (eld d)) \* 
      arr_x_val px_val (Lab (2, 0) (eld d))))
      (Q1:=fun hv =>
        (\*_(d <- (label (Lab (2, 0) (ind_seg l))))
          \[hv d = val_int (nth (abs l) Lval)]) \*
        (\*_(d <- (label (Lab (2, 0) (ind_seg l))))
          (arr_x_ind px_ind (Lab (2, 0) (eld d)) \* 
          arr_x_val px_val (Lab (2, 0) (eld d)))) \* \Top).
    2: xsimpl.
    1:{
      eapply htriple_conseq.
      1: apply htriple_union_pointwise with (Q:=
        fun d hv => 
            \[hv d = val_int (nth (abs l) Lval)] \*
            arr_x_ind px_ind d \* arr_x_val px_val d \* \Top).
      3: xsimpl.
      2:{
        intros d Hin.
        apply wp_equiv.
        rewrite -> wp_ht_eq with (fs:=(single d tt)) (ht1:=fun d0 => rli_func (eld d0) px_ind px_val) 
          (ht2:=(fun=> ((rli_func (eld d)) px_ind px_val))).
        2:{
          introv HH. rewrite -> indom_single_eq in HH. by subst.
        }
        destruct d as (ll, d). 
        rewrite indom_label_eq in Hin. destruct Hin as (<- & Hin).
        unfold ind_seg in Hin.
        rewrite -> indom_interval in Hin.
        apply wp_equiv. simpl. 
        eapply htriple_conseq. 1: eapply rli_func_spec with (a:=l).
        4: xsimpl. 
        4:{ xsimpl; intros. auto. }
        all: try math.
        destruct Hin as (Hin1 & Hin2). split.
        { rewrite <- H_Lind_first. transitivity (nth (abs l) Lind); auto.
          replace 0%nat with (abs 0%Z) by math. apply H_Lind_inc'; math.
        }
        { rewrite <- H_Lind_last. 
          enough (nth (abs (l + 1)) Lind <= nth (abs M) Lind)%Z by math.
          apply H_Lind_inc'; math.
        }
      }
      1:{ intros. by rewrite -> H. }
      1:{
        xsimpl. intros hv. rewrite -> ! hbig_fset_hstar. xsimpl. 
      }
    }
    xsimpl. intros hv.
    rewrite -> hstar_fset_pure. xsimpl. intros. 

    (* now, only a single thing is left *)
    unfold nwp. simpl. rewrite -> union_empty_r.
    match goal with |- himpl _ (wp _ (htrm_of (cons (Lab _ (FH _ ?ht)) _)) _) => pose (ff:=ht) end.
    rewrite -> wp_ht_eq with (ht2:=ff).
    2:{ 
      intros (ll, d) HH. rewrite indom_label_eq in HH. 
      destruct HH as (<- & HH). 
      subst ff. unfold htrm_of. simpl. case_if; eqsolve.
    }
    subst ff. simpl.

    admit.
  }
Admitted.

Lemma htriple_sequ2 (fs fs' : fset D) H Q' Q ht ht1 ht2 htpre ht'
  (Hdj : disjoint fs fs')
  (Hhtpre : forall d, indom fs d -> htpre d = ht1 d)
  (Hhtpre' : forall d, indom fs' d -> htpre d = ht' d)
  (Htppre : htriple (fs \u fs') htpre H Q') (* hv? *)
  (Hht : forall d, indom fs d -> ht d = trm_seq (ht1 d) (ht2 d))
  (Hht' : forall d, indom fs' d -> ht d = ht' d)
  (Htp2 : forall hv, htriple fs ht2 (Q' hv) Q) (* too strong? *)
  (Hcong : forall hv1 hv2, (forall d, indom fs d -> hv1 d = hv2 d) -> 
    Q hv1 ==> Q hv2) :
  htriple (fs \u fs') ht H Q.
Proof using.
  apply wp_equiv.
  rewrite -> union_comm_of_disjoint. 2: apply Hdj.
  rewrite <- wp_union. 2: rewrite -> disjoint_comm; apply Hdj.
  rewrite -> wp_ht_eq with (ht2:=ht').
  2: apply Hht'.
  rewrite -> wp_ht_eq with (ht2:=htpre).
  2: introv HH; rewrite -> Hhtpre'; try reflexivity; try apply HH.
  apply wp_equiv.

  eapply htriple_conseq.
  3:{ 
    hnf. intros v. 
    eapply himpl_trans.
    1: apply wp_seq.
    rewrite -> wp_ht_eq with (ht1:=ht) (ht2:=fun d => trm_seq (ht1 d) (ht2 d)).
    2: apply Hht.
    apply himpl_refl.
  }
  1:{ 
    apply wp_equiv.
    eapply wp_conseq. hnf. intros.
    match goal with |- himpl _ (wp ?fs _ ?ff) => 
      eapply himpl_trans with (H2:=wp fs htpre ff) end.
    1: apply himpl_refl.
    rewrite -> wp_ht_eq with (ht1:=ht1) (ht2:=htpre).
    2: introv HH; rewrite -> Hhtpre; try reflexivity; try apply HH.
    apply himpl_refl.
  }
  apply wp_equiv in Htppre.
  rewrite -> union_comm_of_disjoint in Htppre. 2: apply Hdj.
  rewrite <- wp_union in Htppre. 2: rewrite -> disjoint_comm; apply Hdj.
  eapply himpl_trans.
  1: apply Htppre.
  apply wp_conseq.
  hnf. intros. apply wp_conseq.
  hnf. intros. apply wp_equiv. 
  eapply htriple_conseq.
  1: apply Htp2.
  1: xsimpl.
  hnf. intros. apply Hcong.
  intros. unfold uni. case_if; try reflexivity.
  exfalso. revert H0 C. apply disjoint_inv_not_indom_both. 
  apply Hdj.
Qed.

Lemma ntriple_sequ2 (fs fs' : fset D) H Q' Q ht ht1 ht2 htpre ht'
  (Hdj : disjoint fs fs')
  (Hhtpre : forall d, indom fs d -> htpre d = ht1 d)
  (Hhtpre' : forall d, indom fs' d -> htpre d = ht' d)
  (Htppre : htriple (fs \u fs') htpre H Q') (* hv ? *)
  (Hht : forall d, indom fs d -> ht d = trm_seq (ht1 d) (ht2 d))
  (Hht' : forall d, indom fs' d -> ht d = ht' d)
  (Htp2 : forall hv, htriple fs ht2 (Q' hv) Q)
  (Hcong : forall hv1 hv2, (forall d, indom fs d -> hv1 d = hv2 d) -> 
    Q hv1 ==> Q hv2) :
  htriple (fs \u fs') ht H Q.
Proof using.

(* ? *)
(*
  rewrite <- wp_union in Htppre. 2: apply Hdj.


  pose proof (wp_union (fun hr2 =>
    wp fs ht2 (fun hr3 : D -> val => Q ((hr2 \u_ fs') hr3))) htpre Hdj) as Htmp.
  simpl in Htmp.
  Unset Printing Notations.
  

  rewrite -> disjoint_comm in Hdj.

  rewrite -> wp_union.
    
    eapply himpl_trans with .
      
    pose proof (wp_union (fun=> Q') htpre Hdj) as Htmp.
    simpl in Htmp.
    rewrite -> Htmp. clear Htmp.
    apply wp_equiv.
    apply Htppre.
  }

    rewrite -> wp_union.


  wp_seq

  eapply htriple_conseq.


  apply wp_equiv.

  rewrite <- wp_union. 2: apply Hdj.
  rewrite -> wp_ht_eq with (ht2:=fun d => trm_seq (ht1 d) (ht2 d)).
  2: apply Hht.

  apply wp_equiv.
  (* eapply htriple_seq with (H1:=wp fs' htpre (fun=> Q')). *)
  eapply htriple_seq.
   (* with (H1:=Q'). *)
  1:{
    eapply htriple_conseq.
    1: apply wp_equiv.
    1: rewrite -> wp_ht_eq with (ht1:=ht1) (ht2:=htpre).
    2: introv HH; rewrite -> Hhtpre; try reflexivity; try apply HH.

    evar (q : hhprop).
    
    
    eapply htriple_conseq with (Q':=(fun hr1 => wp fs' htpre (fun=> Q'))).
    1:{
      apply wp_equiv.
      rewrite -> wp_ht_eq with (ht1:=ht1) (ht2:=htpre).
      2: introv HH; rewrite -> Hhtpre; try reflexivity; try apply HH.
      pose proof (wp_union (fun=> Q') htpre Hdj) as Htmp.
      simpl in Htmp.
      rewrite -> Htmp. clear Htmp.
      apply wp_equiv.
      apply Htppre.
    }
    1: apply himpl_refl.
    hnf. intros. apply wp_conseq.
    hnf. intros. apply himpl_refl.
    (* apply Hcong. 
    intros. unfold uni. case_if; try reflexivity.
    exfalso. revert H0 C. apply disjoint_inv_not_indom_both. rewrite -> disjoint_comm. apply Hdj. *)
  }
  eapply htriple_conseq.

  1: apply Htp2.
  1:{ wp himpl





  apply wp_equiv.
  eapply htriple_seq with (H1:=wp fs' htpre (fun=> Q')).
  1:{ 
    eapply htriple_conseq with (Q':=(fun hr1 =>
      wp fs' htpre (fun hr2 => Q' ((hr1 \u_ fs) hr2)))).
    1:{
      apply wp_equiv.
      rewrite -> wp_ht_eq with (ht1:=ht1) (ht2:=htpre).
      2: introv HH; rewrite -> Hhtpre; try reflexivity; try apply HH.
      rewrite -> wp_union.
      2: apply Hdj.
      apply wp_equiv.
      apply Htppre.
    }
    1: apply himpl_refl.
    hnf. intros. apply wp_conseq.
    hnf. intros. apply Hcong. 
    intros. unfold uni. case_if; try reflexivity.
    exfalso. revert H0 C. apply disjoint_inv_not_indom_both. rewrite -> disjoint_comm. apply Hdj.
  }
  eapply htriple_conseq.
  1: apply Htp2 with (hv:=fun=> val_unit).





    

  1: htriple_proj

  xwp. xseq.

  apply wp_equiv.
  eapply htriple_conseq.
  1: apply 



  2: auto.
  apply wp_equiv.
*)
Goal forall (px_ind px_val : loc),
  ntriple 
    ((\*_(d <- ⟨pair 1 0, single 0 tt⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))) \*
     (\*_(d <- ⟨pair 2 0, interval 0 N⟩) 
      ((arr_x_ind px_ind d) \* (arr_x_val px_val d))))
    ((Lab (pair 1 0) (FH (single 0 tt) (fun=> (rlsum_func px_ind px_val)))) :: 
      (Lab (pair 2 0) (FH (interval 0 N) (fun i => (rli_func i px_ind px_val)))) :: 
      nil)
    (fun hv => \[hv (Lab (pair 1 0) 0) = 
      fset_fold (val_int 0) 
        (fun d acc => val_int_add acc (hv d))
        (label (Lab (pair 2 0) (interval 0 N)))] \* \Top).
Proof.
  intros.
  unfold rlsum_func, rli_func.
  (* simplify 1 first *)
  apply (xfocus_lemma (pair 1 0)); simpl; try apply xnwp0_lemma.
  rewrite -> union_empty_r.
  (* little change *)
  rewrite -> wp_ht_eq with (ht2:=(fun=> (rlsum_func px_ind px_val))).
  2:{ intros. unfolds label. 
    (* coercion: eld *)
    (* TODO extract this out to be a lemma *)
    rewrite -> indom_Union in H. 
    setoid_rewrite -> indom_single_eq in H.
    destruct H as (? & <- & <-).
    simpl. rewrite -> indom_single_eq. case_if. auto.
  }
  (* do app2 for rlsum *)
  apply wp_equiv. eapply htriple_eval_like.
  1: apply eval_like_app_fun2; eqsolve.
  (* subst pushdown *)
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  rewrite -> ! For_subst; try eqsolve. 
  (* assign location *)
  eapply htriple_let.
  1:{ 
    rewrite <- hstar_hempty_l at 1.
    eapply htriple_frame. apply htriple_ref.
  }
  intros.
  (* fold *)
  remember (For _ _ _) as ee.
  simpl.
  (* s -> (v d); use funext *)
  match type of Heqee with _ = For _ _ ?b => remember b as body end.
  subst ee.
  replace (fun d : D => (trm_seq (subst "s" (v1 d) (For 0 M body))
      (val_get (v1 d)))) with 
    (fun d : D => (trm_seq (For 0 M (subst "s" (v1 d) body))
      (val_get (v1 d)))).
  2:{ extens. intros. rewrite <- For_subst; try eqsolve. }
  subst body.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  (* simplify hexists *)
  apply wp_equiv.
  xsimpl. intros ps ->. xsimpl.
  (* use only one point location of ps; then forget ps *)
  remember (ps (Lab (1, 0) 0)) as ps0.
  erewrite -> wp_ht_eq with (ht2:=
    fun=> trm_seq (For 0 M (rlsum_loopbody px_ind px_val ps0)) (<{ ! ps0 }>)).
  2:{ 
    intros. unfolds label, rlsum_loopbody. 
    rewrite -> indom_Union in H. 
    setoid_rewrite -> indom_single_eq in H.
    destruct H as (? & <- & <-).
    simpl. by subst ps0.
  }
  apply wp_equiv.
  eapply htriple_conseq.
  3: apply qimpl_refl.
  2:{
    apply himpl_frame_l with (H1':=ps0 ~⟨(1%Z, 0%Z), 0⟩~> 0). subst ps0.
    apply himpl_refl.
  }
  clear ps Heqps0.

  

  eapply htriple_seq.
  1:{

  
  
  
  with (H1:=(nwp
  (cons
     {|
       lab := pair 2 0;
       el :=
         {|
           fs_of := interval 0 N;
           ht_of :=
             fun i : IntDom.type =>
             val_fun "x_ind"
               (trm_fun "x_val"
                  (trm_let "j" (val_ref 0)
                     (trm_seq
                        (While
                           (val_lt
                              (val_array_get "x_ind"
                                 (val_get (val_add "j" 1))) i)
                           (val_set "j" (val_add (val_get "j") 1)))
                        (val_array_get "x_val" "j")))) px_ind px_val
         |}
     |} nil)
  (fun hr' : forall _ : D, val =>
   hstar (hstar
     (hpure
        (eq
           (uni (label {| lab := pair 1 0; el := single 0 tt |}) (fun _ => val_unit) hr'
              {| lab := pair 1 0; el := 0 |})
           (fset_fold 0
              (fun (d : IntDom.type) (acc : Z) =>
               Z.add acc
                 match
                   uni (label {| lab := pair 1 0; el := single 0 tt |}) (fun _ => val_unit)
                     hr' {| lab := pair 2 0; el := d |}
                 with
                 | val_int n => n
                 | _ => 0
                 end) (interval 0 N)))) 
          (ps[1](0) ~⟨(1%Z, 0%Z), 0⟩~> ((fset_fold 0
          (fun (d : IntDom.type) (acc : Z) =>
           Z.add acc
             match
               uni (label {| lab := pair 1 0; el := single 0 tt |}) (fun _ => val_unit)
                 hr' {| lab := pair 2 0; el := d |}
             with
             | val_int n => n
             | _ => 0
             end) (interval 0 N))))   ) htop ))).

  apply wp_equiv. 
  

  xunfocus.



  

  Unset Printing Notations.


  (* apply wp_equiv. *)

  match goal with |- himpl _ (wp _ ?ht _) => pose (ff:=ht) end.
  erewrite -> wp_ht_eq with (ht2:=
    fun (d : D) => If d = Lab (1, 0) 0 then ff d else 0).
    (* fun (d : D) => If indom (single 0 tt) (eld d) then ff d else 0). *)
  2:{ 
    subst ff.
    intros. unfolds label. 
    rewrite -> indom_Union in H. 
    setoid_rewrite -> indom_single_eq in H.
    destruct H as (? & <- & <-).
    simpl. case_if; eqsolve.
    (*
    intros. unfolds label.
    match goal with |- ?e = _ => set(ee:=e) end.
    pattern d in ee.
    subst ee. 
    match goal with |- ?f d = _ => remember f as ff end.
    instantiate (1:=fun d => If indom (single 0 tt) d then ff d else 0).
    rewrite -> indom_Union in H. 
    setoid_rewrite -> indom_single_eq in H.
    destruct H as (? & <- & <-).
    simpl. rewrite -> indom_single_eq. case_if. auto.
    *)
  }

  xunfocus.


  apply wp_equiv.

  xfocus_lemma
  apply htriple_seq with (H1:=(nwp
  (cons
     {|
       lab := pair 2 0;
       el :=
         {|
           fs_of := interval 0 N;
           ht_of :=
             fun i : IntDom.type =>
             val_fun "x_ind"
               (trm_fun "x_val"
                  (trm_let "j" (val_ref 0)
                     (trm_seq
                        (While
                           (val_lt
                              (val_array_get "x_ind"
                                 (val_get (val_add "j" 1))) i)
                           (val_set "j" (val_add (val_get "j") 1)))
                        (val_array_get "x_val" "j")))) px_ind px_val
         |}
     |} nil)
  (fun hr' : forall _ : D, val =>
   hstar (hstar
     (hpure
        (eq
           (uni (label {| lab := pair 1 0; el := single 0 tt |}) (fun _ => val_unit) hr'
              {| lab := pair 1 0; el := 0 |})
           (fset_fold 0
              (fun (d : IntDom.type) (acc : Z) =>
               Z.add acc
                 match
                   uni (label {| lab := pair 1 0; el := single 0 tt |}) (fun _ => val_unit)
                     hr' {| lab := pair 2 0; el := d |}
                 with
                 | val_int n => n
                 | _ => 0
                 end) (interval 0 N)))) 
          (ps[1](0) ~⟨(1%Z, 0%Z), 0⟩~> ((fset_fold 0
          (fun (d : IntDom.type) (acc : Z) =>
           Z.add acc
             match
               uni (label {| lab := pair 1 0; el := single 0 tt |}) (fun _ => val_unit)
                 hr' {| lab := pair 2 0; el := d |}
             with
             | val_int n => n
             | _ => 0
             end) (interval 0 N))))   ) htop ))).
  
  { 
    apply wp_equiv. 
    admit.
  }
  { 



  eapply htriple_seq. with (H1:=
  (\exists  ps[1](0) ~⟨(1%Z, 0%Z), 0⟩~> 0) \*
   arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
   arr_x_val px_val (⟨(1, 0), 0⟩)%arr \*
   (\*_(d <- interval 0 N)
       arr_x_ind px_ind (⟨(2, 0), d⟩)%arr \*
       arr_x_val px_val (⟨(2, 0), d⟩)%arr))).





  xunfocus. apply wp_equiv.
  eapply htriple_conseq with (Q':=(fun hr : D -> val =>
    \[hr[1](0) = fset_fold 0
        (fun d : IntDom.type =>
        Z.add^~ match hr[2](d) with
                | val_int n => n
                | _ => 0
                end) (interval 0 N)] \* 
    ps[1](0) ~⟨(1%Z, 0%Z), 0⟩~> fset_fold 0
        (fun d : IntDom.type =>
        Z.add^~ match hr[2](d) with
                | val_int n => n
                | _ => 0
                end) (interval 0 N))).
  2: apply himpl_refl.
  2:{
    xsimpl. auto.
  }
  apply wp_equiv.

  (* match goal with |- _ ==> wp (fset_of ?a) (htrm_of ?a) ?c => fold (nwp a c) end. *)

  apply (xfocus_lemma (pair 1 0)); simpl; try apply xnwp0_lemma.

  apply wp_equiv. 
  eapply htriple_conseq.
  3:{
    hnf. intros.
    eapply wp_frame.

  
  with (Q':=(fun hr : D -> val =>
  N-WP [{ [2 | i in interval 0 N =>
          (fun "x_ind" "x_val" => (let "j" = ref 0 in
                                   (While
                                      <{
                                      (val_array_get "x_ind" <{ ! "j" + 1 }>) <
                                      i }> <{ "j" := (! "j") + 1 }>);
                                   (val_array_get "x_val" "j"))) px_ind px_val] }]
        {{ hr', \[(hr \u_ ⟨(1, 0), single 0 tt \u empty⟩) hr'
                    (⟨(1, 0), 0⟩)%arr =
                  fset_fold 0
                    (fun d : IntDom.type =>
                     Z.add^~ match
                               (hr \u_ ⟨(1, 0), single 0 tt \u empty⟩) hr'
                                 (⟨(2, 0), d⟩)%arr
                             with
                             | val_int n => n
                             | _ => 0
                             end) (interval 0 N)] \*
                ps[1](0) ~⟨(1%Z, 0%Z), 0⟩~> fset_fold 0
                                              (fun d : IntDom.type =>
                                               Z.add^~ 
                                               match
                                                 (hr \u_
                                                  ⟨(
                                                  1, 0), 
                                                  single 0 tt \u empty⟩) hr'
                                                  (⟨(2, 0), d⟩)%arr
                                               with
                                               | val_int n => n
                                               | _ => 0
                                               end) 
                                              (interval 0 N) }} )).
  3:{
    instantiate(1:=(fun hr : D -> val =>
    N-WP [{ [2 | i in interval 0 N =>
            (fun "x_ind" "x_val" => (let "j" = ref 0 in
                                     (While
                                        <{
                                        (val_array_get "x_ind" <{ ! "j" + 1 }>) <
                                        i }> <{ "j" := (! "j") + 1 }>);
                                     (val_array_get "x_val" "j"))) px_ind px_val] }]
          {{ hr', \[(hr \u_ ⟨(1, 0), single 0 tt \u empty⟩) hr'
                      (⟨(1, 0), 0⟩)%arr =
                    fset_fold 0
                      (fun d : IntDom.type =>
                       Z.add^~ match
                                 (hr \u_ ⟨(1, 0), single 0 tt \u empty⟩) hr'
                                   (⟨(2, 0), d⟩)%arr
                               with
                               | val_int n => n
                               | _ => 0
                               end) (interval 0 N)] \*
                  ps[1](0) ~⟨(1%Z, 0%Z), 0⟩~> fset_fold 0
                                                (fun d : IntDom.type =>
                                                 Z.add^~ 
                                                 match
                                                   (hr \u_
                                                    ⟨(
                                                    1, 0), 
                                                    single 0 tt \u empty⟩) hr'
                                                    (⟨(2, 0), d⟩)%arr
                                                 with
                                                 | val_int n => n
                                                 | _ => 0
                                                 end) 
                                                (interval 0 N) }} )).
    qimpl himpl






  htriple union

  eapply htriple_conseq with (Q':=(fun hr : D -> val =>
    \exists rrr, 
    \[hr[1](0) = rrr] \*
    \[rrr =
      fset_fold 0
        (fun d : IntDom.type =>
        Z.add^~ match hr[2](d) with
                | val_int n => n
                | _ => 0
                end) (interval 0 N)] \* ps[1](0) ~⟨(1%Z, 0%Z), 0⟩~> rrr)).
  2: apply himpl_refl.
  2:{
    xsimpl. intros. subst. auto.
  }


wp union




  eapply htriple_seq.
  2:{
    
    apply wp_equiv.   
  (* htriple_get
  
  apply wp_equiv. xunfocus. apply himpl_refl. }
  apply wp_equiv. *)
  val_get
  
  eapply htriple_seq with (H1:=
  (\exists  ps[1](0) ~⟨(1%Z, 0%Z), 0⟩~> 0) \*
   arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
   arr_x_val px_val (⟨(1, 0), 0⟩)%arr \*
   (\*_(d <- interval 0 N)
       arr_x_ind px_ind (⟨(2, 0), d⟩)%arr \*
       arr_x_val px_val (⟨(2, 0), d⟩)%arr)).

  trm_seq hforall
hexists_intro
  nwp


  (* simplify the latter part? *)
  (* apply wp_equiv.
  eapply htriple_seq.
  2:{ *)
  (* htriple_get
  
  apply wp_equiv. xunfocus. apply himpl_refl. }
  apply wp_equiv. *)


  (* turn back *)
  xunfocus. simpl.
  

  (* then go for 2 *)
  apply (xfocus_lemma (pair 2 0)); simpl; try apply xnwp0_lemma.
  rewrite -> union_empty_r.
  (* little change *)
  rewrite -> wp_ht_eq with (ht2:=(fun d => ((rli_func (eld d)) px_ind px_val))).
  2:{ intros. unfolds label. 
    rewrite -> indom_Union in H. 
    setoid_rewrite -> indom_single_eq in H.
    simpl in H.
    destruct H as (? & H & <-).
    simpl. case_if; eqsolve.
  }
  unfold rli_func.
  (* do app2 for rlsum *)
  apply wp_equiv. eapply htriple_eval_like.
  1: apply eval_like_app_fun2; eqsolve.
  (* subst pushdown *)
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  (* assign location *)
  eapply htriple_let.
  1:{ 
    rewrite <- hstar_hempty_l at 1.
    eapply htriple_frame. apply htriple_ref.
  }
  intros. simpl.
  (* fold but not using funext *)
  pose (ff:=fun d : D => (trm_seq (While 
    (val_lt (val_array_get px_ind (val_get (val_add (v1 d) 1))) (eld d))
    (val_set (v1 d) (val_add (val_get (v1 d)) 1)) ) (val_array_get px_val (v1 d)))).
  pose (ff2:=ff).
  unfold ff, While, While_aux in ff2. simpl in ff2.
  assert (ff = ff2) as Htmp by (unfold ff, ff2; reflexivity).
  unfold ff, ff2 in Htmp. rewrite <- Htmp. clear Htmp ff ff2.
  (* simplify hexists *)
  apply wp_equiv.
  xsimpl. intros pj ->. xsimpl.
  xunfocus.

  wp hstar

  xcleanup.



  apply wp_equiv.




  (* now do some while *)
  eapply htriple_seq.
  (* eapply htriple_seq with (H1:=
  ((\*_(d <- interval 0 N) pj[2](d) ~⟨(2%Z, 0%Z), d⟩~> 0) \*
    ps[1](0) ~⟨(1%Z, 0%Z), 0⟩~> 0 \*
    arr_x_ind px_ind (⟨(1, 0), 0⟩)%arr \*
    arr_x_val px_val (⟨(1, 0), 0⟩)%arr \*
    (\*_(d <- interval 0 N)
        arr_x_ind px_ind (⟨(2, 0), d⟩)%arr \*
        arr_x_val px_val (⟨(2, 0), d⟩)%arr))). *)
  1:{ 
    apply wp_equiv.
    eapply wp_while_hbig_op.




  
  remember (While _ _) as ee.
  simpl. subst ee. rewrite -> ! For_subst; try eqsolve.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  cbn delta [subst] beta iota zeta.
  case_var; try eqsolve.
  
  


  eapply xunfocus_lemma. 1: auto. 1: reflexivity.

  1:{ intros. extens. intros. 
  (* before turning back,  *)
  match goal with |- himpl _ (wp _ ?ht _) => pose (ff:=ht) end.
  erewrite -> wp_ht_eq with (ht2:=
    fun (d : D) => If d = Lab (1, 0) 0 then ff d else 0).
    (* fun (d : D) => If indom (single 0 tt) (eld d) then ff d else 0). *)
  2:{ 
    subst ff.
    intros. unfolds label. 
    rewrite -> indom_Union in H. 
    setoid_rewrite -> indom_single_eq in H.
    destruct H as (? & <- & <-).
    simpl. case_if; eqsolve.
    (*
    intros. unfolds label.
    match goal with |- ?e = _ => set(ee:=e) end.
    pattern d in ee.
    subst ee. 
    match goal with |- ?f d = _ => remember f as ff end.
    instantiate (1:=fun d => If indom (single 0 tt) d then ff d else 0).
    rewrite -> indom_Union in H. 
    setoid_rewrite -> indom_single_eq in H.
    destruct H as (? & <- & <-).
    simpl. rewrite -> indom_single_eq. case_if. auto.
    *)
  }
  (* turn back *)
  eapply xunfocus_lemma with (ht:=fun d => ff (Lab (pair 1 0) d)). 1: auto.
  1:{ intros. extens. intros. case_if. 
  1: intros. 1: reflexivity.



  cbn delta -[For] beta iota zeta. intros.
  

  
  
  wp hexists
  apply wp_equiv. 
  xunfocus.
  
  apply htriple_hexists. intros ->.




  cbn delta [subst] iota beta.

  apply wp htriple.

  xwp.
  simpl.

  xnsimpl.
  (* xunfocus. *)

  



    hstar_fset_Lab
hbig_fset labeled

Module WithArray (Dom : Domain).

Module Export RS := Reasoning(Dom).

Implicit Types P : Prop.
Implicit Types H : hhprop.
Implicit Types Q : val->hhprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i n : int.
Implicit Type v : val.
Implicit Type L : list val.
Implicit Types z : nat.


