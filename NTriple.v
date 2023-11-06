From SLF Require Import LibSepSimpl LibSepReference LibSepTLCbuffer.
From SLF Require Import Fun LabType LibSepReference LibWP Struct Loops.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Set Implicit Arguments.

Lemma htriple_letu2 {D : Type} (fs fs' : fset _) H Q' Q ht ht1 ht2 htpre ht' x
  (Hdj : disjoint fs fs')
  (Hhtpre : forall d, indom fs d -> htpre d = ht1 d)
  (Hhtpre' : forall d, indom fs' d -> htpre d = ht' d)
  (Htppre : htriple (fs \u fs') htpre H Q') (* hv? *)
  (Hht : forall d, indom fs d -> ht d = trm_let (x d) (ht1 d) (ht2 d))
  (Hht' : forall d, indom fs' d -> ht d = ht' d)
  (Htp2 : forall hv, htriple fs (fun d => subst (x d) (hv d) (ht2 d)) (Q' hv) (fun hr => Q (uni fs' hv hr))) :
  (* (Hcong : forall hv1 hv2, (forall d, indom (fs \u fs') d -> hv1 d = hv2 d) -> 
    Q hv1 ==> Q hv2) : *)
  @htriple D (fs \u fs') ht H Q.
Proof using All.
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
    1: apply wp_let.
    rewrite -> wp_ht_eq with (ht1:=ht) (ht2:=fun d => trm_let (x d) (ht1 d) (ht2 d)).
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
  hnf. intros.
  (*   have {}Htppre: H ==> wp fs' htpre (fun=> wp fs htpre Q').
  { apply: himpl_trans; last apply:wp_union2; autos*. }
  (* 2: rewrite -> disjoint_comm; apply Hdj. *)
  eapply himpl_trans.
  1: apply Htppre.
  apply wp_conseq.
  hnf. intros. apply wp_conseq.
  hnf. intros. 
  xapp=> hv.
  move=> ?; apply:applys_eq_init; f_equal; extens=> ?; rewrite /uni.
  do? case:classicT=> //. *)
  erewrite wp_ht_eq.
  { xapp=> hv. 
    move=> ?; apply:applys_eq_init; f_equal; extens=> ?; rewrite /uni.
    do? case:classicT=> //. } 
  move=> ? IN /=. 
  rewrite /uni; case: classicT=> // /(disjoint_inv_not_indom_both _ IN).
  case; autos*.
Qed.

Lemma ntriple_letu2 {D : Type} (s : _) H Q' Q fsht x
  (t1 t2 : trm) (i : int)
  (Htppre : 
    ntriple H
      (Lab (pair i 0) (FH (`{s}) (fun=>t1)) :: 
       fsht)
    Q')
  (Htp2 : forall hv, 
    htriple (label (Lab (pair i 0) (`{s}))) (fun d => subst x (hv[`i](s)) t2) 
      (Q' hv) (fun hr => Q (uni (fset_of fsht) hv hr)))
  :
  ~ has_lab fsht (i,0) ->
  @ntriple D H
    (Lab (pair i 0) (FH (`{s}) (fun d => trm_let x t1 t2)) :: 
    fsht)
    Q.
Proof using All.
  (* move/hasnt_lab. *)
  move=> HNL.
  unfold ntriple, nwp.
  simpl fset_of.
  erewrite -> wp_ht_eq.
  1: apply wp_equiv.
  1: eapply htriple_letu2 with 
    (ht1:=fun=> t1)
    (ht2:=fun=> t2)
    (htpre:=uni (label (Lab (pair i 0) (`{s}))) (fun=> t1)
      (htrm_of fsht))
    (ht:=uni (label (Lab (pair i 0) (`{s}))) (fun d => trm_let x t1 t2)
      (htrm_of fsht))
    (ht':=htrm_of fsht).
  { rewrite (hasnt_lab _ _ HNL); exact/fset_htrm_label_remove_disj. }
  { intros. unfold uni. case_if; try reflexivity. contradiction. }
  { move=> ?; rewrite (hasnt_lab _ _ HNL) /uni; case: classicT=> //.
    move=>/(@disjoint_inv_not_indom_both _ _ _ _ _)/[apply]-[].
    exact/fset_htrm_label_remove_disj. }
  2:{
    intros. unfold uni. case_if; try reflexivity. contradiction.
  }
  2:{ move=> ?; rewrite (hasnt_lab _ _ HNL) /uni; case: classicT=> //.
    move=>/(@disjoint_inv_not_indom_both _ _ _ _ _)/[apply]-[].
    exact/fset_htrm_label_remove_disj. }
  3:{ case=> *; by rewrite /uni /= indom_label_eq. }
  2: { move=> hr /=. 
    rewrite -wp_equiv label_single wp_single -label_single wp_equiv.
    apply/Htp2. }
  unfold ntriple, nwp in Htppre.
  simpl fset_of in Htppre.
  apply wp_equiv.
  erewrite -> wp_ht_eq in Htppre.
  1: apply Htppre.

  intros d H0. destruct d as (ll, d).
  rewrite -> indom_union_eq, -> ! indom_label_eq in H0. 
  unfold htrm_of, uni. rewrite ! indom_label_eq. simpl. repeat case_if; try eqsolve.
Qed.

Lemma xletu2 {D : Type} (s : _) H Q' Q fsht x
  (t1 t2 : trm) (i : int)
  (Htppre : 
    ntriple H
      (Lab (pair i 0) (FH (`{s}) (fun=>t1)) :: 
       fsht)
    Q')
  (Htp2 : forall hv, 
    htriple (label (Lab (pair i 0) (`{s}))) (fun d => subst x (hv[`i](s)) t2) 
      (Q' hv) (fun hr => Q (lab_fun_upd hr hv (i,0))))
  :
  ~ has_lab fsht (i,0) ->
  @ntriple D H
    (Lab (pair i 0) (FH (`{s}) (fun d => trm_let x t1 t2)) :: 
    fsht)
    Q.
Proof.
  move=> ?; apply/ntriple_letu2; eauto=> hv.
  rewrite -wp_equiv -/(fs_of (FH (`{s}) (fun=> subst x (hv[`i](s)) t2))).
  rewrite -/(ht_of (FH (`{s}) (fun=> subst x (hv[`i](s)) t2))) xnwp1_lemma /=.
  rewrite -xnwp1_lemma/=; apply:himpl_trans; last exact/wp_hv.
  xapp=> hr. xsimpl (lab_fun_upd hr hv (i,0))=> ?; apply:applys_eq_init; f_equal.
  extens=> -[??] /=; rewrite /uni; case: classicT.
  { erewrite (hasnt_lab fsht); eauto=> /(@indom_remove _ _ _ _ _)=> lN.
    case E: (lab_eqb _ _)=> //; move: lN; rewrite -lab_eqbE E //. }
  case: classicT=> //; rewrite indom_label_eq indom_single_eq=> -[]->.
  by rewrite eqbxx.
Qed.

Lemma xnapp_lemma' : forall {D : Type} fs_ht Q1 H1 H Q,
  ntriple H1 fs_ht Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  @ntriple D H fs_ht Q.
Proof using.
  introv tE M W.
  apply/xapp_lemma; autos*.
  by rewrite -wp_equiv.
Qed.

Tactic Notation "xnapp" constr(E) ident(hv) := 
  rewrite -> ?hbig_fset_hstar;
  apply/xletu2=> //=; [eapply xnapp_lemma'; 
       [eapply E|
         let hp := fresh "hp" in 
         let HE := fresh "HE" in 
        remember hpure as hp eqn:HE;
       xapp_simpl=> ?; rewrite HE; exact: himpl_refl]|move=> hv; rewrite -wp_equiv]; eauto; simpl.

Tactic Notation "xnapp" constr(E) := 
  let hv := fresh "hv" in xnapp E hv.

Lemma wp_prod_single {A B : Type} s fs Q ht (l : labType):
  @wp (labeled (A * B)) (label (Lab l (`{s} \x fs))) ht Q = 
  @wp (labeled (A * B)) (label (Lab l (`{s} \x fs))) (fun ld => ht(Lab l (s, (eld ld).2))) Q.
Proof. apply/wp_ht_eq; case=> ?[>]; indomE=> /= -[<-][<-]//. Qed.

Lemma hstar_fset_prod1fs {A B D : Type} (l : A) (fs : fset B) : 
  hbig_fset hstar (`{l} \x fs) = 
  fun Q : _ -> hhprop D => \*_(d <- fs) (Q (l, d)).
Proof.
  apply/fun_ext_1=> Q.
  elim/fset_ind: fs. 
  { by rewrite prodfs0 ?hbig_fset_empty. }
  move=> fs x IH ?; rewrite prodfsS hbig_fset_union //.
  { by rewrite hbig_fset_update // IH prod11 hstar_fset_label_single. }
  apply/disjoint_of_not_indom_both=> -[]??; rewrite ?indom_prod /= ?indom_single_eq.
  by case=> ?<-[_].
Qed.

Hint Rewrite @hstar_fset_prod1fs : hstar_fset.
