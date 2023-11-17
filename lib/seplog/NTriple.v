From LGTM.lib.theory Require Import LibFunExt LibLabType LibListExt LibSepTLCbuffer LibSummation.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl LibArray LibLoops LibArray.
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

Import List.

Lemma ntriple_frame_array D H fs_ht H' 
  (fs : list int) (p : loc) f g d S : 
  (0 <= S) ->
  (forall i, In i fs -> 0 <= i < S) ->
  (forall i v, ~ In i fs -> f i = g v i) ->
  (H = H' (harray_fun_int f p S d)) ->
  (forall X, H' X = (H' hempty) \* X) ->
  H' (\*_(i <- fset_of_list fs) (p + 1 + abs i)%nat ~(d)~> f i) ==> 
    nwp fs_ht (fun (v : labeled D -> val) => (\*_(i <- fs) (p + 1 + abs i)%nat ~(d)~> g v i) \* \Top) ->
  ntriple H fs_ht (fun hv => (harray_fun_int (g hv) p S d) \* \Top).
Proof.
  move=> ? IN NIN HE HE' ?.
  set Q := 
    (\*_(i <- diff `[0,S] (fset_of_list fs)) (p + 1 + abs i)%nat ~(d)~> f i) \*
    hheader (abs S) p d.
  have E: (fset_of_list fs \+ `[0, S] \- fset_of_list fs) = `[0, abs S].
  { apply/fset_extens=> x; indomE; rewrite diff_indom. indomE.
    split.
    { case=> [/IN|]; lia. }
    case: (classicT (In x fs))=> [/[dup]?/IN|]; autos*.
    right; splits*; lia. }
  apply/(@ntriple_conseq_frame2 _ Q); eauto.
  { rewrite HE HE' (HE' (hbig_fset _ _ _)). xsimpl.
    rewrite /Q /harray_fun_int /harray_int /harray.
    rewrite hcellsE_int length_map length_List_length ?length_lof'. 
    xsimpl. rewrite -hbig_fset_union //; last (rewrite disjoint_comm; exact/diff_disj).
    rewrite E; erewrite hbig_fset_eq. xsimpl. 
    by move=> ?; indomE=> ?; rewrite nth_lof. }
  move=> v.
  rewrite /Q /harray_fun_int /harray_int /harray.
  xsimpl.
  rewrite hcellsE_int length_map length_List_length ?length_lof'.
  xsimpl.
  erewrite hbig_fset_eq with (fs := `[0,S] \- fset_of_list fs); first last. 
  { move=> ?; rewrite diff_indom; indomE=> -[]*; rewrite (NIN _ v) //. }
  rewrite -hbig_fset_union //; last (rewrite disjoint_comm; exact/diff_disj).
  rewrite E; erewrite hbig_fset_eq. xsimpl. 
  by move=> ?; indomE=> ?; rewrite nth_lof.
Qed.

Tactic Notation "xframe_array" constr(p) uconstr(s) := 
    let Q1 := fresh "Q1" in 
    let HEQ1 := fresh "Q" in 
    match goal with 
    | |- context[harray_fun_int ?f p ?S ?d] =>
    set (QH1 := harray_fun_int f p S d);
    remember QH1 as Q1 eqn: HEQ1 in |- *;
    rewrite -?HEQ1
    end;
    eapply ntriple_frame_array with (p := p) (fs := s); 
      [ |
        |
        |
        let h := fresh "h" in 
        let f := fresh "h" in 
        match goal with |- ?x = ?y => set (h := x) end;
        pattern Q1 in h;
        set (f := fun _ => _) in h;
        simpl in h;
        rewrite /h HEQ1;
        reflexivity
      | intro=> /=; xsimpl*
      |
      ]; clear Q1 HEQ1; simpl; try xsimpl.


Lemma wp_ret D : forall t1 (v : val) Q H (fs : fset D),
    htriple fs t1 H (fun hr => Q (fun=> v)) -> 
    htriple fs (fun d => trm_seq (t1 d) v) H Q.
Proof using.
  move=> *.
  rewrite -wp_equiv. 
  apply: himpl_trans; last apply: wp_seq.
  rewrite wp_equiv. apply: htriple_conseq; eauto.
  move=> ?. rewrite wp_equiv. apply/htriple_val.
  exact: himpl_refl.
Qed.


Lemma eqbxx l : lab_eqb l l = true.
Proof. exact/eqbxx. Qed.

Lemma xunfocus_lemma' D (Q : (labeled D -> val) (*-> (HD -> val)*) -> _) fs_hts 
  (ht : D -> trm) (fs : fset D) H (ht' : labeled D -> _)
  (l : labType) :
  ~ has_lab fs_hts l ->
  (ht = (fun d => ht' (Lab l d))) ->
  (* adequate (fun hr => Q hr hr) (⟨l, fs⟩ \u fset_of fs_hts) -> *)
  ntriple H ((Lab l (FH fs ht)) :: fs_hts) (fun hr => Q hr) ->
  H ==> wp ⟨l, fs⟩ ht' (fun=> nwp fs_hts (fun hr' => Q hr')).
Proof.
  rewrite /ntriple/nwp=> /hasnt_lab /[dup]rE {1}-> /[! @fset_of_cons] htE.
  apply: himpl_trans_r.
  apply: himpl_trans; first  apply wp_union2.
  {  exact/fset_htrm_label_remove_disj. }
  under wp_ht_eq=> -[l' d] IN.
  { unfold label in IN. rewrite -> indom_Union in IN. 
    setoid_rewrite -> indom_single_eq in IN.
    simpl in IN.
    destruct IN as (? & ? & IN). injection IN as <-. subst.
    (* move: (htE l)=> /(congr1 (@^~ d)) {}htE. *)
    rewrite (@lookup_eq _ l) rE ?lookup_cons // ?lookup_cons_ht ?lookup_cons_fs //=. 
    { rewrite rE. over. }
    unfold label. rewrite -> indom_Union. eauto. } 
  move=> /= h Hwp; simpl; apply/wp_conseq; eauto=> hr /=; simpl.
  (* xpull=> hv' {Hwp}h Hwp; exists hv'. *)
  (* move: h Hwp. *)
  under wp_ht_eq=> ? IN.
  { rewrite (@remove_eq _ l) /= eqbxx /= // -rE; over. }
  rewrite -rE // => {Hwp}h Hwp.
Qed.

Tactic Notation "xunfocus'" := 
eapply xunfocus_lemma'=> //=.

Tactic Notation "xret" := 
rewrite wp_equiv; apply wp_ret;
apply/htriple_conseq; [|exact: himpl_refl
|intro; xcleanup 1; exact: himpl_refl]; rewrite -wp_equiv /=.

Tactic Notation "xin" constr(S1) ":" tactic(tac) := 
  let n := constr:(S1) in
  xfocus (n,0)%Z; tac; try(
  first [xunfocus | xunfocus' | xcleanup n]; simpl; try apply xnwp0_lemma); rewrite -?xntriple1_lemma /=.

Tactic Notation "xfor_sum_cong_solve3" :=
  let hvE1 := fresh "hvE1" in
  let hvE2 := fresh "hvE2" in
  let someindom := fresh "someindom" in
  intros ???? hvE1 hvE2;  (try case_if=> //; [ ]);  
  indomE; f_equal; f_equal;
  match goal with 
  | |- Sum ?a _ = Sum ?a _ => apply fold_fset_eq; intros ?; indomE; intros someindom; extens; intros 
  | _ => idtac
  end; try (rewrite hvE1 1?hvE2; 
  [eauto|autorewrite with indomE; try math; 
    (first [ apply someindom | idtac ])| autorewrite with indomE; try math; 
    (first [ apply someindom | idtac ])]; simpl; try lia).
Tactic Notation "xstart" :=   
  let Inv := fresh "Inv" in 
  let R1 := fresh "R1" in 
  let R2 := fresh "R2" in 
  xset_Inv Inv 1; xset_R_core int R1 2; xset_R_core int R2 3; xset_clean Inv R1 R2.


Tactic Notation "xfor_bigsrt" constr(Inv) constr(R1) constr(R2) constr(H) constr(H') :=
  eapply (@xfor_lemma_gen2_bigstr _ _ Inv R1 R1 R2 R2 _ _ _ _ H H');
  [ intros ??; rewrite ?/Inv ?/R1 ?/R2; xnsimpl
  | 
  |
  |
  | 
  | 
  |
  |
  | xfor_sum_cong_solve3
  | 
  |
  |
  |
  |
  |
  | 
  |
  |
  |
  |rewrite ?/Inv ?/R1 ?/R2; rewrite -> ?hbig_fset_hstar; rewrite ?Union_same; try lia; try do ? xsimpl*
  | intros ?; rewrite ?/Inv ; rewrite -> ?hbig_fset_hstar; xsimpl
  ]=> //; try (solve [ rewrite ?/Inv ?/R1 ?/R2 /=; xlocal ]); autos*; try math.

Lemma hbig_fset_list D (fs : list int) :
    NoDup fs ->
    @hbig_fset D int hstar fs = 
    fun (H : _ -> hhprop D) =>
    \*_(i <- `[0,length fs]) H (fs[i]).
Proof.
  move=> nd; apply/fun_ext_1=> ?.
  rewrite (fset_of_list_nodup 0 nd) hbig_fset_Union.
  { apply/hbig_fset_eq=> ??.
    rewrite update_empty hbig_fset_update // hbig_fset_empty. 
    xsimpl*. }
  disjointE=> ??? /((NoDup_nthZ _ _).1 nd). lia.
Qed.

Hint Rewrite hbig_fset_list : hstar_fset.

Ltac xstep := xwp; xapp.
Ltac xgo := do ? xstep.
Tactic Notation "xapp*" constr(E) := xwp; xapp_big E=> //.
Tactic Notation "xin*" constr(S1) ":" tactic(tac) := 
  let n := constr:(S1) in
  xfocus (n,0)%Z; try rewrite wp_prod_single /=; tac; try(
  first [xunfocus | xcleanup n]; simpl; try apply xnwp0_lemma); rewrite -?xntriple1_lemma /=.