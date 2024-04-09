Set Implicit Arguments.
From LGTM.lib.theory Require Export LibCore LibSepTLCbuffer.
From LGTM.lib.seplog Require Export LibSepVar LibSepFmap.
From LGTM.lib.theory Require Import LibFunExt LibLabType.
From LGTM.lib.seplog Require Import LibSepSimpl LibSepReference.

From mathcomp Require Import ssreflect ssrfun zify.

Declare Custom Entry wp.

Open Scope Z_scope.

Global Hint Extern 1 (_ = _ :> hheap _) => fmap_eq.

Section I_didnt_come_up_with_a_name.

Context {D : Type}.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hlocal] *)

Lemma hbig_fset_empty {A} hop (f : A -> hhprop D) :
  hbig_fset hop empty f = \[].
Proof.
  by rewrite /hbig_fset fset_foldE.
Qed.

(* Check hstar_assoc. *)

Lemma hbig_fset_update {A} hop fs x (f : A -> hhprop D) :
  ~ Fmap.indom fs x ->
  (forall h1 h2, hop h1 h2 = hop h2 h1) ->
  (forall h1 h2 h3, hop (hop h1 h2) h3 = hop h1 (hop h2 h3)) ->
  hbig_fset hop (update fs x tt) f = hop (f x) (hbig_fset hop fs f).
Proof.
  move=> ? C AS.
  rewrite /hbig_fset fset_foldE //.
  move=> *. rewrite -?AS; fequals.
Qed.

Hint Resolve hstar_hempty_l hstar_hempty_r hstar_assoc hstar_comm : core.

Lemma hsubst_hstar_fset f g (H : D -> (hhprop D)) fs :
  cancel f g ->
  cancel g f -> 
  \{x |-> f x} \*_(d <- fs) H d = \*_(d <- fs) \{x |-> f x} H d.
Proof.
  move=> c1 c2.
  elim/fset_ind: fs.
  { by rewrite ?hbig_fset_empty (hsubst_hempty c1 c2). }
  move=> fs x IH ?.
  by rewrite ?hbig_fset_update // (hsubst_hstar _ _ c1 c2) IH.
Qed.

Lemma hbig_fset_union {A} hop (fs1 fs2 : fset A) (f : A -> (hhprop D)) :
  comm hop ->
  assoc hop ->
  (forall h, hop \[] h = h) ->
  disjoint fs1 fs2 ->
  hbig_fset hop (fs1 \u fs2) f = hop (hbig_fset hop fs1 f) (hbig_fset hop fs2 f).
Proof.
  move=> ?? hop0; elim/fset_ind: fs1.
  { rewrite hbig_fset_empty union_empty_l hop0 //. }
  move=> > IH ? /[! @disjoint_update]-[??].
  rewrite -update_union_not_r' ?hbig_fset_update // ?indom_union_eq; autos*.
  rewrite IH //; xsimpl.
Qed.

Lemma hbig_fset_part {A : Type} (fs : fset A) (P : A -> Prop) : 
  hbig_fset hstar fs = 
  fun (H : _ -> hhprop D) => hbig_fset hstar (fs ∩ P) H \* hbig_fset hstar (fs ∖ P) H.
Proof.
  apply/fun_ext_1=> ?; rewrite -hbig_fset_union // ?fs_pred_part //.
  exact/fs_pred_part_disj.
Qed.

Lemma hbig_fset_eq {A} hop (fs : fset A) (f1 f2 : A -> (hhprop D)) :
  (forall d, indom fs d -> f1 d = f2 d) ->
  hbig_fset hop fs f1 = hbig_fset hop fs f2.
Proof. move=> E; by apply/fold_fset_eq=> ?? /[!E]. Qed.

Lemma hbig_fset_emptys {A} hop (fs : fset A) :
  comm hop ->
  assoc hop ->
  (forall h : hhprop D, hop \[] h = h) ->
  hbig_fset hop fs (fun _ => \[]) = \[].
Proof.
  move=> ?? hop0.
  elim/fset_ind: fs=> [|?? E ?].
  { exact/hbig_fset_empty. }
  by rewrite hbig_fset_update // E hop0.
Qed.

Lemma hbig_fset_hstar {A} (fs : fset A) (P Q : _ -> hhprop D): 
  \*_(d <- fs) P d \* Q d = (\*_(d <- fs) P d) \* (\*_(d <- fs) Q d).
Proof.
  elim/fset_ind: fs=> [|?? E ?].
  { rewrite ?hbig_fset_empty. xsimpl. }
  rewrite ?hbig_fset_update // E; xsimpl.
Qed.

Lemma hstar_fset_pure {A} (fs : fset A) P: 
  \*_(d <- fs) \[P d] = \[forall d, indom fs d -> P d] :> hhprop D.
Proof.
  elim/fset_ind: fs=> [|??].
  { rewrite hbig_fset_empty.
    apply/fun_ext_1=> ?; apply/prop_ext; split.
    { move->.
      have p: (forall a, indom (empty : fset A) a -> P a) by [].
      by exists p. }
  by case. }
  move=> E ?; rewrite hbig_fset_update // E.
  apply/fun_ext_1=> x; apply/prop_ext; split.
  { case=> ? [?] [][?] E1 [][?] E2 [].
    eexists.
    { move=> ?; rewrite indom_update_eq=> -[<-|]; eauto. }
    subst. rewrite E1 E2 /hempty; autos*. }
  case=> p ->; exists (empty : hheap D), (empty : hheap D); splits~.
  all: eexists=> //*; apply/p; rewrite* indom_update_eq.
Qed.

Lemma hstar_fset_pure_hstar {A} (fs : fset A) P H: 
   \*_(d <- fs) \[P d] \* H d = \[forall d, indom fs d -> P d] \* \*_(d <- fs) H d :> hhprop D.
Proof. by rewrite hbig_fset_hstar hstar_fset_pure. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hlocal] *)

Lemma local_union h1 h2 (fs : fset D) :
  local fs (h1 \u h2) = 
  (local fs h1 /\ local fs h2).
Proof.
  apply/prop_ext; split=> l.
  { split=> x d ?; apply/(l x); rewrite* indom_union_eq. }
  move=> x d; by rewrite* indom_union_eq.
Qed.

Fact local_union_fs_l {A} (fs1 fs2 : fset A) h : 
  local fs1 h -> local (fs1 \u fs2) h.
Proof.
  intros. unfolds local.
  intros. rewrite indom_union_eq. left. by eapply H; eauto.
Qed.

Fact local_union_fs_r {A} (fs1 fs2 : fset A) h : 
  local fs2 h -> local (fs1 \u fs2) h.
Proof.
  intros. unfolds local.
  intros. rewrite indom_union_eq. right. by eapply H; eauto.
Qed.

Lemma local_merge h1 h2 (fs : fset D) m :
  local fs (merge m h1 h2) = 
  (local fs h1 /\ local fs h2).
Proof.
  apply/prop_ext; split=> l.
  { split=> x d ?; apply/(l x); rewrite* indom_merge_eq. }
  move=> x d; by rewrite* indom_merge_eq.
Qed.

Lemma hconseq_local (L : list val) p (d : D) : local (single d tt) (hconseq L p d).
Proof.
  revert p d. induction L; intros.
  { rewrite -> hconseq_nil. unfolds local, indom, map_indom. simpl. eqsolve. }
  { rewrite -> hconseq_cons. rewrite local_union. split; auto. 
    hnf. intros ? ?. rewrite ! indom_single_eq. eqsolve. }
Qed. 

Implicit Type (d : D) (H : hhprop D).


Lemma hlocal_hsingle p x fs d: 
  indom fs d ->
  hlocal (p ~(d)~> x) fs.
Proof. by move=> ?? -> ?? /[! indom_single_eq]-[?<-]. Qed.

Lemma hlocal_hsingle_single p x d: 
  hlocal (p ~(d)~> x) (single d tt).
Proof. exact/hlocal_hsingle/indom_single. Qed.

Lemma hlocal_hstar H1 H2 fs : 
  hlocal H1 fs -> hlocal H2 fs ->
  hlocal (H1 \* H2) fs.
Proof.
  move=> hl1 hl2 ? [?] [?] [/hl1 ?] [/hl2 ?] [_ ->].
  by rewrite* local_union.
Qed.

Lemma hlocal_hmerge H1 H2 fs m vd : 
  hlocal H1 fs -> hlocal H2 fs ->
  hlocal (H1 \(m, vd) H2) fs.
Proof.
  move=> hl1 hl2 ? [?] [?] [/hl1 ?] [/hl2 ?][_]->.
  by rewrite* local_merge.
Qed.

Lemma hlocal_hempty fs : hlocal (\[] : hhprop D) fs.
Proof. by move=> ? ->. Qed.

Lemma hlocal_hpure P fs : hlocal (\[P] : hhprop D) fs.
Proof. by move=> ? [?->]. Qed.

Lemma hlocal_hstar_fset {A} (P : A -> (hhprop D)) fs1 fs2: 
  (forall a, indom fs1 a -> hlocal (P a) fs2) ->
    hlocal (\*_(a <- fs1) P a) fs2.
Proof.
  elim/fset_ind: fs1.
  { rewrite hbig_fset_empty=> *; exact/hlocal_hempty. }
  move=> fs d IHfs ? IN. rewrite hbig_fset_update //.
  apply/hlocal_hstar/IHfs=> *; apply/IN; by rewrite* indom_update_eq.
Qed.

Lemma hlocal_hmerge_fset {A} (P : A -> (hhprop D)) fs1 fs2 m vd:
  comm m -> assoc m -> 
  (forall x y, (vd x /\ vd y) <-> vd (m x y)) ->
  (forall (d : A), indom fs1 d -> hlocal (P d) fs2) ->
    hlocal (\(m, vd)_(d <- fs1) P d) fs2.
Proof.
  move=> ???.
  elim/fset_ind: fs1.
  { rewrite hbig_fset_empty=> *; exact/hlocal_hempty. }
  move=> fs d IHfs ? IN. rewrite hbig_fset_update //.
  apply/hlocal_hmerge/IHfs=> *; apply/IN; by rewrite* indom_update_eq.
  { move=>*. exact/hmerge_comm. }
  move=>*. exact/hmerge_assoc.
Qed.

Lemma hlocal_hexists A fs (J : A -> hhprop D) :
  (forall x, hlocal (J x) fs) -> hlocal (hexists J) fs.
Proof. by move=> hl ? [? /hl]. Qed.

Lemma hlocal_hforall A `{Inhab A} fs (J : A -> hhprop D)  :
  (forall x, hlocal (J x) fs) -> hlocal (hforall J) fs.
Proof. by move=> hl ? /hforall_inv-/(_ arbitrary)/(hl arbitrary). Qed.

Lemma hlocal_union_l H fs1 fs2 : hlocal H fs1 -> hlocal H (fs1 \u fs2).
Proof.
  intros. hnf in H0 |- *. intros. apply H0 in H1.
  by apply local_union_fs_l.
Qed.

Lemma hlocal_union_r H fs1 fs2 : hlocal H fs2 -> hlocal H (fs1 \u fs2).
Proof.
  intros. hnf in H0 |- *. intros. apply H0 in H1.
  by apply local_union_fs_r.
Qed.

Lemma hhtop_intro fs H h : hlocal H fs -> H h -> hhtop fs h.
Proof.
  intros. hnf. exists H. rewrite <- union_empty_r.
  by apply hstar_intro.
Qed.

Lemma hhtop_intro' fs h : local fs h -> (hhtop fs : hhprop D) h.
Proof.
  intros. hnf. exists (fun h' => h = h'). rewrite <- union_empty_r.
  apply hstar_intro; auto. apply hpure_intro. hnf. by intros ? ->.
Qed.

Lemma hhtop_inv fs h : hhtop fs h -> exists H : (hhprop D), hlocal H fs /\ H h.
Proof.
  intros. hnf in H. destruct H as (H & Hh).
  apply hstar_inv in Hh.
  destruct Hh as (h1 & h2 & Hh1 & Hh2 & Hdj & ->).
  apply hpure_inv in Hh2. destruct Hh2 as (Hh2 & ->).
  setoid_rewrite union_empty_r.
  eauto.
Qed.

Lemma hhtop_hlocal fs : hlocal (hhtop fs : hhprop D) fs.
Proof.
  hnf. intros h Hh. apply hhtop_inv in Hh.
  destruct Hh as (? & Ha & Hb). by apply Ha in Hb.
Qed.

Lemma hhtop_hstar fs1 fs2 : hhtop (fs1 \u fs2) = hhtop fs1 \* (hhtop fs2 : hhprop D).
Proof.
  xsimpl.
  { hnf. intros h Hh. apply hhtop_inv in Hh.
    destruct Hh as (H & Hl & Hh). apply Hl in Hh.
    pose (P:=fun (x : hloc D) (_ : val) => indom fs1 (snd x)).
    rewrite <- filter_union_compl with (P:=P) (fs:=h).
    pose proof (filter_compl_disjoint h P) as Hdj.
    apply hstar_intro; try assumption.
    { apply hhtop_intro with (H:=fun h' => h' = filter P h).
      2: reflexivity.
      hnf. intros ? ->. subst P. hnf. intros ? ? HH. apply filter_indom' in HH.
      simpl in HH. firstorder.
    }
    { apply hhtop_intro with (H:=fun h' => h' = filter (fun (x : hloc D) (y : val) => ~ P x y) h).
      2: reflexivity.
      hnf. intros ? ->. subst P. hnf. intros ? ? HH. apply filter_indom' in HH.
      simpl in HH. 
      hnf in Hh. destruct HH as (? & ? & Hin & Hnotin). apply Hh in Hin.
      rewrite indom_union_eq in Hin. intuition.
    }
  }
  { hnf. intros h Hh. apply hstar_inv in Hh.
    destruct Hh as (h1 & h2 & Hh1 & Hh2 & Hdj & ->).
    apply hhtop_inv in Hh1, Hh2.
    destruct Hh1 as (H1 & Hl1 & Hh1), Hh2 as (H2 & Hl2 & Hh2).
    eapply hhtop_intro with (h:=h1 \u h2) (H:=H1 \* H2).
    { apply hlocal_hstar; try (by apply hlocal_union_l); try (by apply hlocal_union_r). }
    { by apply hstar_intro. }
  }
Qed.

End I_didnt_come_up_with_a_name.

Hint Resolve hstar_hempty_l hstar_hempty_r hstar_assoc hstar_comm : core.

(** From now on, all operators have opaque definitions. *)

Global Opaque hempty hpure hstar hsingle hexists hforall
              hwand qwand htop hgc haffine.
