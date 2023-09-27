(** * Struct: Arrays and Records *)

Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer.
From SLF Require Import Fun LabType.
From mathcomp Require Import ssreflect ssrfun.
Hint Rewrite conseq_cons' : rew_listx.

Module WithArray (Dom : Domain).

Module Export NS := nReasoning(Dom).

Implicit Types P : Prop.
Implicit Types H : hhprop.
Implicit Types Q : val->hhprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i n : int.
Implicit Type v : val.
Implicit Type L : list val.
Implicit Types z : nat.

(* a list of cells at index d *)
Fixpoint hcells (L:list val) (p:loc) (d : D) : hhprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~(d)~> x) \* (hcells L' (p+1)%nat d)
  end.

Definition hheader := 
  (fun (k:nat) (p:loc) (d : D) => p ~(d)~> (val_header k) \* \[(p, d) <> null d]).
Fact hheader_def :
  hheader = (fun (k:nat) (p:loc) (d : D) => p ~(d)~> (val_header k) \* \[(p, d) <> null d]).
Proof eq_refl.

Definition harray (L:list val) (p:loc) (d : D) : hhprop :=
  hheader (length L) p d \* hcells L (p+1)%nat d.

Definition harray_int (L:list int) (p:loc) (d : D) : hhprop :=
  harray (LibList.map val_int L) p d.

Definition val_array_length : val := val_length.

Module Export Realization.

Definition least_feasible_array_loc h L p (d : D) :=
  forall p', disjoint (Fmap.hconseq L p' d) h -> (p', d) <> null d -> (p <= p')%Z.

Lemma hheader_intro : forall p k d,
  (p, d) <> null d ->
  (hheader k p d) (Fmap.single (p, d) (val_header k)).
Proof using.
  introv N. rewrite hheader_def. rewrite hstar_hpure_r.
  split*. applys hsingle_intro.
Qed.

Lemma hheader_inv: forall h p k d,
  (hheader k p d) h ->
  h = Fmap.single (p, d) (val_header k) /\ (p, d) <> null d.
Proof using.
  introv E. rewrite hheader_def in E. rewrite hstar_hpure_r in E.
  split*.
Qed.

Lemma hlocal_hheader (l : nat) p d : hlocal (hheader l p d) (single d tt).
Proof.
  unfold hlocal. 
  hnf; intros h Hh; apply hheader_inv in Hh; destruct Hh as (-> & ?); 
  apply local_single.
Qed.

Lemma hheader_not_null : forall p k d,
  hheader k p d ==> hheader k p d \* \[(p, d) <> null d].
Proof using. intros. rewrite hheader_def. xsimpl*. Qed.

(* Transparent Fmap.hconseq.
Arguments Fmap.hconseq : simpl nomatch.
Arguments LibList.map : simpl nomatch. *)

Lemma hcells_intro : forall L p d,
  (hcells L p d) (Fmap.hconseq L p d).
Proof using.
  intros L. induction L as [|L']; intros; rew_listx; simpl.
  { applys hempty_intro. }
  { simpl. applys hstar_intro.
    { applys* hsingle_intro. }
    { replace (p+1)%nat with (S p) by math. applys IHL. }
    { applys Fmap.disjoint_single_hconseq. left. math. } }
Qed.

Lemma hcells_inv : forall p L h d,
  hcells L p d h ->
  h = Fmap.hconseq L p d.
Proof using.
  introv N. gen p h. induction L as [|x L'];
   intros; rew_listx; simpls.
  { applys hempty_inv N. }
  { lets (h1&h2&N1&N2&N3&->): hstar_inv N. fequal.
    { applys hsingle_inv N1. }
    { replace (p+1)%nat with (S p) in * by math. applys IHL' N2. } }
Qed.

Lemma harray_intro : forall k p L d,
  k = length L ->
  (p, d) <> null d ->
  (harray L p d) (Fmap.hconseq (val_header k :: L) p d).
Proof using.
  introv E n. unfold harray. rew_listx. applys hstar_intro.
  { subst k. applys* hheader_intro. }
  { replace (p+1)%nat with (S p) in * by math. applys hcells_intro. }
  { applys disjoint_single_hconseq. left. math. }
Qed.

Lemma harray_inv : forall p L h d,
  (harray L p d) h ->
  h = (Fmap.hconseq (val_header (length L) :: L) p d) /\ (p, d) <> null d.
Proof using.
  introv N. unfolds harray. rew_listx.
  lets (h1&h2&N1&N2&N3&->): hstar_inv (rm N).
  replace (p+1)%nat with (S p) in * by math.
  lets (N4&Np): hheader_inv (rm N1).
  lets N2': hcells_inv (rm N2). subst*.
Qed.

Lemma hlocal_hcells (L : list val) p d : hlocal (hcells L p d) (single d tt).
Proof.
  unfold hlocal. 
  hnf; intros h Hh; apply hcells_inv in Hh; subst h; apply hconseq_local.
Qed.

Lemma hlocal_harray (L : list val) p d : hlocal (harray L p d) (single d tt).
Proof. unfold harray; hlocal. apply hlocal_hheader. apply hlocal_hcells. Qed.

Lemma hconseq_least_fresh (h : hheap D) L d :
  exists p, 
    Fmap.disjoint (Fmap.hconseq L p d) h /\ 
    least_feasible_array_loc h L p d /\ (p, d) <> null d.
Proof using.
  pose proof (ex_min _ (hconseq_least_fresh_pre h L d (fun d : D => null d))) as (p & H & H0).
  exists p. unfold least_feasible_array_loc. intuition.
Qed.

(* this part heavily follows the ref and free part. *)
Lemma hoare_alloc_nat : forall d H k,
  hoare d (val_alloc k)
    H
    (fun r => (\exists p, \[r = val_loc p] \* harray (LibList.make k val_uninit) p d) \* H).
Proof using.
  intros. intros h Hh.
  pose proof (hconseq_least_fresh h (val_header k :: (LibList.make k val_uninit)) d)
    as (p & Hdj & Hls & Hnn).
  hnf in Hls.
  eexists. exists (val_loc p). split.
  { eapply eval1_alloc. 1-2: reflexivity. all: auto. }
  { applys~ hstar_intro.
    exists p. rewrite~ hstar_hpure_l. split~. apply~ harray_intro. by rewrite -> length_make.
  }
Qed.

Lemma hhoare_alloc_nat : forall fs H (k : D -> nat),
  hhoare fs (fun d => (val_alloc (k d)))
    H
    (fun hr => (\*_(d <- fs) \exists p, \[hr d = val_loc p] \* harray (LibList.make (k d) val_uninit) p d) \* H).
Proof using.
  intros.
  replace H with ((\*_(_ <- fs) \[]) \* H) at 1; last by rewrite hbig_fset_emptys //.
  apply (hhoare_hstar_fset _ (fun d v => \exists p, \[v = _] \* _))=> *; autos~.
  { apply hlocal_hexists. unfolds hlocal. intros. hnf. intros. rewrite -> hstar_hpure_l in H0.
    destruct H0 as (_ & H0). apply harray_inv in H0. destruct H0 as (-> & ?).
    apply hconseq_local.
  }
  { replace (\[] \* H) with H by xsimpl. apply hoare_alloc_nat. }
Qed.

(** We then derive the Separation Logic reasoning rule. *)

Lemma htriple_alloc_nat : forall fs (k : D -> nat),
  htriple fs (fun d => (val_alloc (k d)))
    \[]
    (fun hr => (\*_(d <- fs) \exists p, \[hr d = val_loc p] \* harray (LibList.make (k d) val_uninit) p d)).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_alloc_nat; xsimpl~.
Qed.

Hint Resolve htriple_alloc_nat : htriple.

Lemma hoare_dealloc : forall H L p d,
  hoare d (val_dealloc p)
    (harray L p d \* H)
    (* here, added some detail *)
    (fun v => \[v = val_unit] \* H).
Proof using.
  intros. intros h Hh. destruct Hh as (h1&h2&N1&N2&N3&N4). subst h.
  exists h2 val_unit. split; [|rewrite -> hstar_hpure_l; auto].
  applys* eval1_dealloc L. applys harray_inv N1.
Qed.

Lemma hhoare_dealloc : forall fs H L (p : D -> loc),
  hhoare fs (fun d => val_dealloc (p d))
    ((\*_(d <- fs) harray L (p d) d) \* H)
    (fun hr => \[hr = fun _ => val_unit] \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_fset_pure=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _])); autos~.
  1:{ intros. unfolds hlocal. intros h Hh. 
    apply harray_inv in Hh. destruct Hh as (-> & ?). apply hconseq_local.
  }
  move=> d ?. 
  apply/hoare_conseq; by [apply hoare_dealloc|eauto|xsimpl].
Qed.

Lemma htriple_dealloc : forall fs L (p : D -> loc),
  htriple fs (fun d => val_dealloc (p d))
    (\*_(d <- fs) harray L (p d) d)
    (fun hr => \[hr = fun _ => val_unit]).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_dealloc; xsimpl~.
Qed.

Hint Resolve htriple_dealloc : htriple.

Section Properties_hcell.

Context (d : D).

Lemma hcells_nil_eq : forall p,
  hcells nil p d = \[].
Proof using. auto. Qed.

Lemma hcells_cons_eq : forall p x L,
  hcells (x::L) p d = (p ~(d)~> x) \* hcells L (p+1)%nat d.
Proof using. intros. simpl. xsimpl*. Qed.

Lemma hcells_one_eq : forall p x L,
  hcells (x::nil) p d = (p ~(d)~> x).
Proof using. intros. rewrite -> hcells_cons_eq, hcells_nil_eq. xsimpl. Qed.

Lemma hcells_concat_eq : forall p L1 L2,
  hcells (L1++L2) p d = (hcells L1 p d \* hcells L2 (length L1 + p)%nat d).
Proof using.
  intros. gen p. induction L1; intros; rew_list; simpl.
  { xsimpl. }
  { rewrite IHL1. math_rewrite (length L1 + (p + 1) = S (length L1 + p))%nat.
    xsimpl. }
Qed.

Lemma hcells_focus : forall k p L,
  k < length L ->
  hcells L p d ==>
       ((p+k)%nat ~(d)~> LibList.nth k L)
    \* (\forall w, ((p+k)%nat ~(d)~> w) \-* hcells (LibList.update k w L) p d).
Proof using.
  introv E. gen k p. induction L as [|x L']; rew_list; intros.
  { false. math. }
  { simpl. rewrite nth_cons_case. case_if.
    { subst. math_rewrite (p + 0 = p)%nat. xsimpl. intros w.
      rewrite update_zero. rewrite hcells_cons_eq. xsimpl. }
    { forwards R: IHL' (k-1)%nat (p+1)%nat. { math. }
      math_rewrite ((p+1)+(k-1) = p+k)%nat in R. xchange (rm R).
      xsimpl. intros w. xchange (hforall_specialize w).
      rewrite update_cons_pos; [|math]. rewrite hcells_cons_eq. xsimpl. } }
Qed.

Corollary hcells_focus_nochange : forall k p L,
  k < length L ->
  hcells L p d ==>
       ((p+k)%nat ~(d)~> LibList.nth k L)
    \* (((p+k)%nat ~(d)~> LibList.nth k L) \-* hcells L p d).
Proof using.
  intros. eapply himpl_trans. 1: apply hcells_focus with (k:=k); auto.
  apply himpl_frame_r.
  apply himpl_hforall_l with (x:=nth k L).
  rewrite -> update_nth_same; auto.
Qed.

End Properties_hcell.

Lemma harray_focus : forall (d : D) k p L,
  k < length L ->
  harray L p d ==>
       ((p+1+k)%nat ~(d)~> LibList.nth k L)
    \* (\forall w, ((p+1+k)%nat ~(d)~> w) \-* harray (LibList.update k w L) p d).
Proof using.
  introv E. unfolds harray. xchanges (>> hcells_focus E). intros w.
  xchange (hforall_specialize w). xsimpl. rewrite* length_update.
Qed.

Lemma harray_focus_nochange : forall (d : D) k p L,
  k < length L ->
  harray L p d ==>
       ((p+1+k)%nat ~(d)~> LibList.nth k L)
    \* (((p+1+k)%nat ~(d)~> LibList.nth k L) \-* harray L p d).
Proof using.
  introv E. unfolds harray. eapply himpl_trans. 1: apply harray_focus.
  1: apply E.
  apply himpl_frame_r. xchange (hforall_specialize (LibList.nth k L)).
  rewrite -> update_nth_same; auto.
Qed.

Lemma hoare_ptr_add : forall (d : D) p n H,
  p + n >= 0 ->
  hoare d (val_ptr_add p n)
    H
    (fun r => \[r = val_loc (abs (p + n))] \* H).
Proof using. introv N. apply hoare_binop, evalbinop_ptr_add. rewrite -> abs_nonneg; math. Qed.

Lemma eval1_length_sep : forall s s2 p k (d : D),
  s = Fmap.union (Fmap.single (p, d) (val_header k)) s2 ->
  @eval1 D d s (val_length (val_loc p)) s (val_int k).
Proof using.
  introv ->. forwards Dv: Fmap.indom_single p (val_header k).
  applys eval1_length.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma hoare_length : forall H k p (d : D),
  hoare d (val_length p)
    ((hheader k p d) \* H)
    (fun r => \[r = val_int k] \* (hheader k p d) \* H).
Proof using.
  intros. intros s K0. exists s (val_int k). split.
  { destruct K0 as (s1&s2&P1&P2&D&U). lets (E1&N): hheader_inv P1.
    subst s1. applys eval1_length_sep U. }
  { rewrite~ hstar_hpure_l. }
Qed.

(* analogous to get operation *)
Lemma hhoare_length : forall fs H (k : D -> nat) (p : D -> loc),
  hhoare fs (fun d => val_length (p d))
    ((\*_(d <- fs) (hheader (k d) (p d) d)) \* H)
    (fun hr => \[hr = k] \* (\*_(d <- fs) (hheader (k d) (p d) d)) \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_assoc -hstar_fset_pure_hstar=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _] \* _)); autos~.
  1:{ intros. unfolds hlocal. intros h Hh. 
    apply hheader_inv in Hh. destruct Hh as (-> & ?). apply local_single.
  }
  1:{ intros. unfolds hlocal. intros h Hh. rewrite -> hstar_hpure_l in Hh. 
    destruct Hh as (_ & Hh).
    apply hheader_inv in Hh. destruct Hh as (-> & ?). apply local_single.
  }
  move=> d ?. 
  apply/hoare_conseq; by [apply hoare_length|eauto|xsimpl].
Qed.

Lemma htriple_length : forall fs (k : D -> nat) (p : D -> loc),
  htriple fs (fun d => val_length (p d))
    (\*_(d <- fs) (hheader (k d) (p d) d))
    (fun hr => \[hr = k] \* (\*_(d <- fs) (hheader (k d) (p d) d))).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_length; xsimpl~.
Qed.

Hint Resolve htriple_length : htriple.

Module Export ArrayAccessDef.
Import ProgramSyntax.
Open Scope wp_scope.

Lemma abs_lt_inbound : forall i k,
  0 <= i < nat_to_Z k ->
  (abs i < k).
Proof using.
  introv N. apply lt_nat_of_lt_int. rewrite abs_nonneg; math.
Qed.

Lemma succ_int_plus_abs : forall p i,
  i >= 0 ->
  ((p + 1 + abs i) = abs (nat_to_Z p + (i + 1)))%nat.
Proof using.
  introv N. rewrite abs_nat_plus_nonneg; [|math].
  math_rewrite (i+1 = 1 + i).
  rewrite <- succ_abs_eq_abs_one_plus; math.
Qed.

Lemma htriple_array_length_header : forall fs (k : D -> nat) (p : D -> loc),
  htriple fs (fun d => val_array_length (p d))
    (\*_(d <- fs) (hheader (k d) (p d) d))
    (fun hr => \[hr = k] \* (\*_(d <- fs) (hheader (k d) (p d) d))).
Proof using. intros. applys htriple_length. Qed.

Lemma htriple_array_length : forall fs (L : D -> list val) (p : D -> loc),
  htriple fs (fun d => val_array_length (p d))
    (\*_(d <- fs) (harray (L d) (p d) d))
    (fun hr => \[hr = (fun d => length (L d))] \* (\*_(d <- fs) (harray (L d) (p d) d))).
Proof using.
  intros. unfold harray. applys htriple_conseq_frame htriple_length.
  { instantiate (1:=(\*_(d <- fs) hcells (L d) (p d + 1)%nat d)). 
    instantiate (1:=(fun d => length (L d))). xsimpl.
    by rewrite -> hbig_fset_hstar.
  }
  { xsimpl; auto. by rewrite -> hbig_fset_hstar. }
Qed.

Definition val_array_get : val :=
  <{ fun 'p 'i =>
       let 'j = 'i + 1 in
       let 'n = val_ptr_add 'p 'j in
       val_get 'n }>.

Lemma htriple_array_get : forall fs (p : D -> loc) (i : D -> int) (v : D -> val) (L : D -> list val),
  (forall d, indom fs d -> 0 <= (i d) < length (L d)) ->
  (forall d, LibList.nth (abs (i d)) (L d) = v d) ->
  htriple fs (fun d => val_array_get (p d) (i d))
    (\*_(d <- fs) (harray (L d) (p d) d))
    (fun hr => \[hr = v] \* (\*_(d <- fs) (harray (L d) (p d) d))).
Proof using.
  introv N E. eapply htriple_eval_like.
  1:{ apply eval_like_app_fun2. intros. eqsolve. }
  simpl.
  eapply htriple_let. 
  1:{ replace (\*_(d <- fs) harray (L d) (p d) d) with 
    (\[] \* \*_(d <- fs) harray (L d) (p d) d) by xsimpl. 
    eapply htriple_frame. apply htriple_add.
  }
  simpl. intros. apply htriple_hpure. intros ->.
  eapply htriple_let. 
  1:{ replace (\*_(d <- fs) harray (L d) (p d) d) with 
    (\[] \* \*_(d <- fs) harray (L d) (p d) d) by xsimpl. 
    eapply htriple_frame. apply htriple_ptr_add. 
    intros. specializes N H. math.
  }
  simpl. intros. apply htriple_hpure. intros ->.
  eapply htriple_conseq. 3: apply qimpl_refl. 
  2:{ apply hbig_fset_himpl.
    intros. apply harray_focus_nochange with (k:=abs (i d)).
    specializes N H. math.
  }
  simpl. erewrite -> hbig_fset_hstar.
  eapply htriple_conseq. 2: apply himpl_refl.
  1:{ apply htriple_frame.
    eapply htriple_conseq. 3: apply qimpl_refl.
    2:{ apply hbig_fset_himpl. intros. 
      replace (p d + 1 + abs (i d))%nat with (abs (p d + (i d + 1))).
      2:{ specializes N H. math. }
      apply himpl_refl.
    } 
    apply htriple_get.
  }
  simpl. hnf. xsimpl. 
  1:{ intros. extens=> ?. by rewrite <- E, -> H. }
  intros ? ->.
  rewrite <- hbig_fset_hstar. 
  apply hbig_fset_himpl.
  intros. 
  replace (p d + 1 + abs (i d))%nat with (abs (p d + (i d + 1))).
  2:{ specializes N H. math. } 
  xsimpl.
Qed.

Definition intr {A : Type} (fs : fset A) (b : A -> Prop) : fset A := (Fmap.filter (fun x _ => b x) fs).


Lemma htriple_if_dep (H : D -> hhprop) (Q : D -> hhprop) f fs : forall (b:D -> bool) t1 t2,
  htriple (intr fs b) t1 
  (
    \*_(d <- (intr fs b)) H d
  )
  (fun hr => 
    \[forall d, b d -> hr d = f d] \*
    \*_(d <- (intr fs b)) Q d
  ) ->

  htriple (intr fs (not \o b)) t2
  (
    \*_(d <- (intr fs (not \o b))) H d
  )
  (fun hr =>
    \[forall d, ~ b d -> hr d = f d] \*
    \*_(d <- (intr fs (not \o b))) Q d
  ) -> 

  htriple fs (fun d => trm_if (b d) (t1 d) (t2 d))
  (
    \*_(d <- fs) H d
  )
  (fun hr =>
    \[hr = f] \*
    \*_(d <- fs) Q d
  ).
Proof.
  introv H1 H2.
  have Dj: disjoint (intr fs (fun x : D => b x)) (intr fs (not \o (fun x : D => b x))).
  { apply/disjoint_of_not_indom_both=> ?;
    rewrite /intr ?filter_indom /=. firstorder. }
  apply/htriple_if.
  have: fs = (intr fs b) \u (intr fs (not \o b)).
  { apply/fset_extens=> x.
    rewrite /intr indom_union_eq ?filter_indom /=.
    case: (classicT (b x)); firstorder. }
  move=> /[dup] fsE->.
  rewrite ?hbig_fset_union //.
  set (Q1 := \*_(d <- intr fs b) Q d).
  set (Q2 := \*_(d <- intr fs (not \o (fun x : D => b x))) Q d).
  apply wp_equiv.
  apply: himpl_trans; last apply/wp_hv.
  xsimpl.
  rewrite -{2}fsE.
  have Impl: 
    (fun hr : D -> val => (\[forall d, indom fs d -> b d -> hr d = f d] \* Q1) \* 
                          (\[forall d, indom fs d -> ~ b d -> hr d = f d] \* Q2)) ===>
    (fun hr : D -> val => \exists g, \[hr \u_fs g = f] \* Q1 \* Q2).
  { xsimpl f=> r r1 r2. extens=> y.
    case: (classicT (indom fs y))=> [/[dup]/(@uni_in _ _ _ _ _ _)|/[dup]/(@uni_nin _ _ _ _ _ _)]-> //.
    case: (classicT (b y)); eauto. }
  apply/wp_equiv/htriple_conseq; last apply/Impl; eauto.
  apply/htriple_union=> //.
  { introv hE. xsimpl=> hf ?? /[dup]/hf<- // ? /[! hE] //.
    by rewrite /intr filter_indom. }
  { introv hE. xsimpl=> hf ?? /[dup]/hf<- // ? /[! hE] //.
    by rewrite /intr filter_indom. }
  { rewrite -wp_equiv (wp_ht_eq _ t1) 1?wp_equiv.
    { apply/htriple_conseq; eauto. 
      by xsimpl=> ? E ?? /E. }
    move=> ?; rewrite /intr filter_indom=> -[?].
    by case: (b _). }
  rewrite -wp_equiv (wp_ht_eq _ t2) 1?wp_equiv.
  { apply/htriple_conseq; eauto. 
    by xsimpl=> ? E ?? /E. }
  move=> ?; rewrite /intr filter_indom=> -[?] /=.
  by case: (b _).
Qed.

Definition val_abs : val :=
  <{ fun 'i => 
     let 'c = 'i < 0 in 
     let 'm = 0 - 1 in
     let 'j = 'm * 'i in
     if 'c then 'j else 'i
  }>.

Lemma htriple_abs `{Inhab D} : forall fs (i : D -> int),
  htriple fs (fun d => val_abs (i d))
    \[]
    (fun hr => \[hr = fun d => abs (i d)]).
Proof.
move=> fs i; apply/wp_equiv.
do 3 (xwp; xapp).
apply/wp_equiv/htriple_conseq;
[apply (@htriple_if_dep (fun=> \[]) (fun=> \[]) (fun d => abs (i d)))| |]; 
rewrite ?hbig_fset_emptys // -1?wp_equiv; try xsimpl*.
{ xwp; xval; xsimpl=> ?.
  move: (i _)=> {}i ?.
  math. }
xwp; xval; xsimpl=> ? /[! istrue_isTrue_eq].
move: (i _)=> {}i ?.
math.
Qed.

Definition read_array : val :=
  <{ fun 'p 'i =>
      let 'i = val_abs 'i in
      let 'l = val_length 'p in
      let 'c = 'i < 'l in
      if 'c then 
        val_array_get 'p 'i
      else 0 }>.

Lemma htriple_array_read `{Inhab D} : forall fs (p : D -> loc) (i : D -> int) (L : D -> list int),
  htriple fs (fun d => read_array (p d) (i d))
    (\*_(d <- fs) (harray_int (L d) (p d) d))
    (fun hr => \[hr = fun d => List.nth (abs (i d)) (L d) 0] \* (\*_(d <- fs) (harray_int (L d) (p d) d))).
Proof using.
move=> ?? i L.
eapply htriple_eval_like.
1:{ apply eval_like_app_fun2. intros. eqsolve. }
simpl.
apply wp_equiv.
(* apply: himpl_trans; last apply wp_hv. *)
simpl.
xwp; xapp htriple_abs.
xwp; xapp htriple_array_length.
xwp; xapp.
rewrite wp_equiv.
apply/htriple_if_dep; rewrite -wp_equiv.
{ apply/xapp_lemma.
  { apply/(htriple_array_get _ _ _ (fun d => LibList.map val_int (L d))); last reflexivity.
    move=> ?. rewrite /intr filter_indom=> -[] ?; math. }
  unfold protect.
  xsimpl=> f-> d.
  rewrite length_map=> Lt.
  replace (abs (abs (i d))) with (abs (i d)); [| math].
  rewrite nth_map; try math; move:Lt.
  move: (abs _) (L _)=> /[swap].
  elim=> // ?. 
  { rewrite length_nil; math. }
  move=> l IHl [|?] /=; rewrite length_cons ?nth_zero // => ?.
  rewrite nth_cons IHl //. rewrite istrue_isTrue_eq. math. }
xwp; xval;xsimpl=>?. rewrite length_map istrue_isTrue_eq=> ?.
rewrite List.nth_overflow // -length_List_length. math.
Qed.

Global Hint Resolve htriple_array_read : htriple.

Definition val_array_set : val :=
  <{ fun 'p 'i 'v =>
       let 'j = 'i + 1 in
       let 'n = val_ptr_add 'p 'j in
       val_set 'n 'v }>.

(* a single point operation *)
Lemma htriple_array_set_pre : forall fs (p : D -> loc) (i : D -> int) (v v' : D -> val),
  (forall d, indom fs d -> 0 <= i d) ->
  htriple fs (fun d => val_array_set (p d) (i d) (v d))
    (\*_(d <- fs) ((p d) + 1 + abs (i d))%nat ~(d)~> v' d)
    (fun=> \*_(d <- fs) ((p d) + 1 + abs (i d))%nat ~(d)~> v d).
Proof using.
  introv E. eapply htriple_eval_like.
  1:{ apply eval_like_app_fun3. all: intros; eqsolve. }
  simpl.
  eapply htriple_let. 
  1:{
    eapply htriple_conseq_frame. 1: apply htriple_add.
    1: xsimpl. apply qimpl_refl.
  }
  simpl. intros. apply htriple_hpure. intros ->.
  eapply htriple_let. 
  1:{ 
    eapply htriple_conseq_frame. 
    1:{ apply htriple_ptr_add. intros. specialize (E _ H). math. }
    1: xsimpl. apply qimpl_refl.
  }
  simpl. intros. apply htriple_hpure. intros ->.
  apply wp_equiv.
  rewrite -> wp_ht_eq with (ht2:=fun d => 
    val_set (val_loc (p d + 1 + abs (i d))%nat) (v d)).
  2:{ intros. f_equal. f_equal. specialize (E _ H).
    f_equal. f_equal. math.
  }
  apply wp_equiv.
  apply htriple_set.
Qed.

Corollary htriple_array_set : forall fs (p : D -> loc) (i : D -> int) (v : D -> val) (L : D -> list val),
  (forall d, indom fs d -> 0 <= (i d) < length (L d)) ->
  (forall d, indom fs d -> LibList.nth (abs (i d)) (L d) = v d) ->
  htriple fs (fun d => val_array_set (p d) (i d) (v d))
    (\*_(d <- fs) (harray (L d) (p d) d))
    (fun=>(\*_(d <- fs) (harray (LibList.update (abs (i d)) (v d) (L d)) (p d) d))).
Proof using.
  introv N E. 
  eapply htriple_conseq. 3: xsimpl.
  2:{ apply hbig_fset_himpl.
    intros. apply harray_focus with (k:=abs (i d)).
    specializes N H. math.
  }
  simpl. rewrite -> hbig_fset_hstar.
  eapply htriple_conseq_frame.
  1: apply htriple_array_set_pre.
  1: intros; by apply N.
  { xsimpl. }
  { xsimpl. rewrite <- hbig_fset_hstar. 
    apply hbig_fset_himpl.
    intros. 
    replace (p d + 1 + abs (i d))%nat with (abs (p d + (i d + 1))).
    2:{ specializes N H. math. }
    xchange (hforall_specialize (v d)).
  }
Qed.

End ArrayAccessDef.

End Realization.

End WithArray.
