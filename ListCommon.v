Set Implicit Arguments.
From mathcomp Require Import ssreflect ssrfun zify.
From SLF Require Import Fun LabType LibSepFmap.
From Coq Require Sorted.

Import List.

Notation "x '[' i ']'" := (List.nth (abs i) x 0) (at level 5, format "x [ i ]").

Fact take_conversion [A : Type] (n : nat) (l : list A) : take n l = firstn n l.
Proof.
  revert n. induction l; intros; simpl in *; rewrite ?take_nil; auto.
  all: destruct n; auto.
  simpl. rewrite ?take_cons. now rewrite IHl.
Qed.

Fact listapp_conversion [A : Type] (l1 l2 : list A) : LibList.app l1 l2 = List.app l1 l2.
Proof. revert l2. induction l1; intros; simpl; auto. now rewrite app_cons_l IHl1. Qed.

Fact nth_error_some_inrange {A : Type} (i : nat) (al : list A) a : 
  nth_error al i = Some a -> i < length al.
Proof.
  revert i a. induction al as [ | a' al IH ]; intros; simpl in *.
  all: destruct i; simpl in *; try discriminate; try lia.
  apply IH in H. lia.
Qed.

Fact Forall2_nth_pointwise [A B : Type] (da : A) (db : B) (la : list A) (lb : list B) (P : A -> B -> Prop) :
  List.Forall2 P la lb <-> (List.length la = List.length lb /\ forall i : nat, (i < List.length la)%nat ->
    P (List.nth i la da) (List.nth i lb db)).
Proof.
  revert lb. induction la as [ | a la' IH ] using List.rev_ind; intros.
  { split; [ intros H | intros (Hl & HP) ].
    { inversion_clear H. simpl. split; auto. intros. lia. }
    { destruct lb; try discriminate. constructor. } }
  { split; [ intros H | intros (Hl & HP) ].
    { pose proof (List.Forall2_length H) as Hl. split; auto.
      apply List.Forall2_app_inv_l in H. destruct H as (lb' & bb & (_ & Hfeq)%IH & Hab & ->).
      inversion Hab; subst. inversion H3; subst. rename y into b.
      rewrite ?List.app_length /= ?Nat.add_1_r in Hl |- *. injection Hl as Hl.
      intros i Hi. destruct (Nat.ltb i (List.length la')) eqn:E.
      { apply Nat.ltb_lt in E. rewrite !List.app_nth1; try lia. now apply Hfeq. }
      { apply Nat.ltb_ge in E. assert (i = List.length lb') as -> by lia.
        rewrite <- Hl at 1. rewrite !List.nth_middle; try lia. assumption. } }
    { rewrite ?List.app_length /= ?Nat.add_1_r in Hl |- *.
      assert (lb <> nil) as (lb' & b & ->)%List.exists_last by (destruct lb; simpl in Hl; eqsolve).
      rewrite ?List.app_length /= ?Nat.add_1_r in Hl, HP. injection Hl as Hl.
      apply List.Forall2_app.
      { apply IH. split; auto. intros i Hi. specialize (HP _ (Peano.le_S _ _ Hi)).
        rewrite !List.app_nth1 in HP; try lia. exact HP. }
      { constructor. 2: constructor. specialize (HP _ (Peano.le_n _)).
        rewrite -> Hl in HP at 2. rewrite !List.nth_middle in HP; try lia. exact HP. } } }
Qed.

Fact nth_map_lt : forall [A B : Type] (da : A) (db : B) (f : A -> B) (l : list A) (n : nat)
  (H : (n < length l)%nat),
  nth n (map f l) db = f (nth n l da).
Proof.
  intros. revert l H. induction n as [ | n IH ]; intros.
  { destruct l; simpl in H; try lia; auto. }
  { destruct l; simpl in H; try lia; auto.
    simpl. apply IH. lia. }
Qed.

Fact nth_In_int (l : list int) (n : int) :
  (0 <= n < length l) -> In (nth (abs n) l 0) l.
Proof. intros H. apply nth_In. math. Qed.

Fact In_nth_int (l : list int) (x : int) :
  In x l -> exists i : int, 0 <= i < length l /\ l[i] = x.
Proof. intros H. apply In_nth with (d:=0) in H. destruct H as (n & Hn & <-). exists n. split; try math. f_equal; math. Qed.

Lemma NoDup_nthZ {A : Type} l (z : A): 
  NoDup l <->
  (forall i j, (0<= i < Datatypes.length l) ->
  (0<= j < Datatypes.length l) -> nth (abs i) l z = nth (abs j) l z -> i = j).
Proof. 
  etransitivity. 1: apply NoDup_nth with (d:=z). 
  split; intros H i j Ha Hb Hc. 
  { enough (abs i = abs j) by math. revert Hc. apply H; math. }
  { enough (Z.of_nat i = Z.of_nat j) by math. apply H; try math.
    replace (abs i) with i by math. replace (abs j) with j by math. assumption. }
Qed.

Lemma in_combineE {A B : Type} (l : list A) (l' : list B) (x : A) (y : B) :
  In (x, y) (combine l l') -> (In x l /\ In y l').
Proof.
  revert l'. induction l as [ | a l IH ]; simpl; intros; try tauto.
  destruct l' as [ | b l' ]; simpl in H |- *; try contradiction.  
  rewrite pair_equal_spec in H. firstorder.
Qed.

Fact list_update_intermediate__ {A : Type} (a : A) (L : list A) (n : nat) (H : (n < length L)%nat) :
  (List.app (repeat a (S n)) (skipn (S n) L)) =
  LibList.update n a (List.app (repeat a n) (skipn n L)).
Proof.
  pose proof (firstn_skipn n L). rewrite <- H0 at 1.
  rewrite -> skipn_app. rewrite -> skipn_all2 at 1.
  all: rewrite firstn_length_le; try math.
  replace (S n - n)%nat with 1%nat by math.
  rewrite -Nat.add_1_r repeat_app. 
  pose proof (skipn_length n L).
  remember (skipn n L) as l eqn:E. destruct l. 1: simpl in H1; math. simpl.
  rewrite -!listapp_conversion. erewrite update_middle.
  3: now rewrite length_List_length repeat_length.
  2: constructor; now exists a0.
  reflexivity.
Qed.

Fact filter_all_false {A : Type} (f : A -> bool) (l : list A) 
  (H : forall x, In x l -> f x = false) : filter f l = nil.
Proof.
  induction l as [ | y l IH ]; simpl in *; auto.
  pose proof (H _ (or_introl eq_refl)) as ->.
  f_equal; auto.
Qed.

Fact nth_firstn {A : Type} [def : A] (l : list A) (n i : nat) (H : (i < n)%nat) :
  nth i (firstn n l) def = nth i l def.
Proof.
  destruct (Nat.ltb n (length l)) eqn:E.
  { apply Nat.ltb_lt in E. 
    pose proof (firstn_skipn n l) as HH. rewrite <- HH at 2.
    rewrite app_nth1 ?firstn_length_le; try math; auto. }
  { apply Nat.ltb_ge in E. rewrite firstn_all2; try math; auto. }
Qed.

Fact nth_skipn {A : Type} [def : A] (l : list A) (n i : nat) (H : (n < length l)%nat) :
  nth i (skipn n l) def = nth (i + n)%nat l def.
Proof.
  pose proof (firstn_skipn n l) as HH. rewrite <- HH at 2.
  rewrite app_nth2 ?firstn_length_le; try math; auto. f_equal; math.
Qed.

Fact last_notnil {A : Type} (a b : A) (l : list A) (H : l <> nil) :
  last (a :: l) b = last l b.
Proof. 
  revert a. induction l; intros; try contradiction.
  destruct l; auto.
Qed.

Fact nth_last {A : Type} (a b : A) (l : list A) (H : l <> nil) :
  nth (length l - 1)%nat l a = last l b.
Proof.
  induction l; intros; try contradiction.
  simpl. destruct l as [ | aa l ]; auto.
  simpl in IHl |- *. assert (aa :: l <> nil) as Htmp by now intros.
  specialize (IHl Htmp). now rewrite Nat.sub_0_r in IHl.
Qed.

Fact nth_nil {A : Type} [d : A] n : List.nth n (@nil A) d = d.
Proof. destruct n; auto. Qed.

Fact last_sufcond : forall def l (P : int -> Prop), l <> nil -> (forall x, In x l -> P x) -> P (last l def).
Proof.
  clear. intros def l P Hneq. induction l; simpl; intros; try contradiction.
  destruct l.
  { apply H. auto. }
  { apply IHl; auto. discriminate. }
Qed.

Fact notnil_length {A : Type} (l : list A) : l <> nil <-> 0 < length l.
Proof. destruct l; simpl; split; intros; try math; try discriminate; try contradiction. Qed.

Section index.

Context {A : Type}.

Implicit Type l s : list A.
(* Implicit Type i : A. *)

Fixpoint index (i : A) l : int :=
  match l with
  | nil => 0
  | x :: l' => If x = i then 0 else (index i l' + 1)
  end.

Lemma index_nodup (def : A) i l : 
  0 <= i < length l ->
  List.NoDup l -> 
    index (nth (abs i) l def) l = i.
Proof.
  revert i. induction l as [ | x l IH ]; intros i Hi Hnodup; simpl in Hi |- *; try math.
  inversion_clear Hnodup.
  remember (abs i) as n eqn:E. destruct n.
  { case_if. math. }
  { replace n with (abs (i-1)) by math. rewrite IH; try math; auto. 
    case_if; try math.
    subst x. false H. apply nth_In. math. }
Qed.

Lemma index_mem x s : (index x s < length s) = (In x s).
Proof.
  induction s as [ | y s IH ]; simpl; try math. rewrite -IH. clear IH. case_if; extens; intuition lia.
Qed.

Lemma index_size x s : index x s <= length s.
Proof. induction s; simpl; auto; try case_if; try math. Qed.

Lemma indexG0 x s : 0 <= index x s.
Proof. induction s; simpl; auto; try case_if; try math. Qed.

Lemma nth_index (def : A) x s : In x s -> nth (abs (index x s)) s def = x.
Proof.
  induction s as [ | y s IH ]; simpl; intros; try contradiction. 
  case_if; auto. destruct H; try contradiction.
  pose proof (indexG0 x s).
  replace (abs (index x s + 1)) with (S (abs (index x s)))%nat by math. auto.
Qed.

Lemma index_app1 x s1 s2 : index x s1 < length s1 -> index x (List.app s1 s2) = index x s1.
Proof.
  induction s1 as [ | y s1 IH ]; simpl; intros; auto; try lia.
  case_if; auto. rewrite IH; math.
Qed.

Lemma index_app_le x s1 s2 : index x s1 <= index x (List.app s1 s2).
Proof.
  induction s1 as [ | y s1 IH ]; simpl; intros; auto; try lia.
  1: apply indexG0. case_if; try math.
Qed.

Corollary in_take x l i : 0 <= i <= length l -> (In x (take (abs i) l)) = (index x l < i).
Proof.
  intros Hi. pose proof (firstn_skipn (abs i) l).
  assert (length (firstn (abs i) l) = abs i :> nat) by (rewrite firstn_length_le; math).
  rewrite -> take_conversion. rewrite <- H at 2.
  extens. split; intros HH.
  { rewrite -index_mem in HH. rewrite index_app1; math. }
  { rewrite -index_mem H0. pose proof (index_app_le x (firstn (abs i) l) (skipn (abs i) l)). math. }
Qed.

Corollary memNindex x s :  ~In x s -> index x s = length s.
Proof. rewrite -index_mem. pose proof (index_size x s). math. Qed.

End index.

Section list_of_fun.

(* some customized theory of from functions to lists *)
Lemma list_of_fun [A : Type] (f : int -> A) (n : int) (H : 0 <= n) :
  @sigT (list A) (fun l =>
    (length l = n :> int /\ (forall (i : int) (def : A), 0 <= i < n -> nth (abs i) l def = f i))).
Proof.
  remember (abs n) as nn eqn:E.
  revert n H E. induction nn as [ | nn IH ]; intros.
  { assert (n = 0) as -> by math. exists (@nil A). split; auto. intros; math. }
  { assert (nn = abs (n - 1)) as Hq by math. apply IH in Hq; try math.
    destruct Hq as (la & H1 & H2). exists (app la (f (n - 1) :: nil)).
    rewrite -> app_length. split; simpl; try math.
    intros i def Hin. destruct (Z.leb (n - 1) i) eqn:E2.
    { apply Z.leb_le in E2. replace i with (n-1) in * by math. 
      replace (abs (n-1)) with (length la) by math. now rewrite nth_middle. }
    { apply Z.leb_gt in E2. rewrite app_nth1. 1: apply H2. all: math. } }
Qed.

Definition list_of_fun' [A : Type] (f : int -> A) (n : int) :
  @sigT (list A) (fun l =>
    (length l = abs n :> int /\ (forall (i : int) (def : A), 0 <= i < abs n -> nth (abs i) l def = f i))).
apply list_of_fun. math. Defined.

Fact lof_make_constfun [A : Type] (c : A) (n : int) :
  (projT1 (list_of_fun' (fun _ => c) n)) = repeat c (abs n).
Proof.
  destruct (list_of_fun' _ _) as (l & Hlen & HH). simpl.
  apply nth_ext with (d:=c) (d':=c).
  1: rewrite repeat_length; math.
  intros i Hi. 
  rewrite -> nth_repeat; try math. rewrite <- HH with (i:=i) (def:=c) at 2; try math.
  f_equal; math.
Qed.

(* TODO possibly change this name? *)
Definition lof f N := projT1 (@list_of_fun' int f N).

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

Lemma In_lof_id N a : In a (lof id N) <-> 0 <= a < abs N.
Proof.
  unfold lof. destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
  split; intros H.
  { apply In_nth with (d:=0) in H. destruct H as (n & Hlt & <-).
    replace n with (abs n) by math. rewrite Hl1; math. }
  { pose proof H as HH%(Hl1 _ 0). rewrite -HH. apply nth_In. math. }
Qed.

Lemma lof_indices {A : Type} (f : int -> A) (g : int -> int) n :
  projT1 (list_of_fun' (f \o g) n) = map f (lof g n).
Proof.
  destruct (list_of_fun' _ _) as (l1 & Hlen1 & Hl1); simpl.
  pose proof (length_lof' g n) as Hlen2.
  apply (nth_ext _ _ (f 0) (f 0)). 
  1: rewrite map_length; math.
  intros n0 Hlt. replace n0 with (abs n0) by math.
  rewrite Hl1 ?(nth_map_lt 0) ?nth_lof //; try math.
Qed.

Corollary lof_indices' {A : Type} (f : int -> A) n :
  projT1 (list_of_fun' f n) = map f (lof id n).
Proof. by rewrite <- lof_indices. Qed.

End list_of_fun.

Section list_interval.

Context {A : Type}.

Implicit Type l : list A.

Definition list_interval (lb rb : nat) l :=
  firstn (rb - lb)%nat (skipn lb l).

Lemma list_interval_length (lb rb : int) l :
  0 <= lb <= rb -> rb <= length l -> length (list_interval (abs lb) (abs rb) l) = rb - lb :> int.
Proof. intros. rewrite /list_interval firstn_length_le ?skipn_length; try math. Qed.

Lemma list_interval_nth (def : A) (x lb rb : int) l :
  0 <= lb <= rb -> rb <= length l -> 0 <= x < rb - lb ->
  nth (abs (lb + x)) l def = nth (abs x) (list_interval (abs lb) (abs rb) l) def.
Proof.
  intros. rewrite /list_interval.
  pose proof (firstn_skipn (abs lb) l) as HH1.
  rewrite <- HH1 at 1. rewrite app_nth2. all: rewrite firstn_length_le; try math.
  replace (abs _ - abs _)%nat with (abs x) by math.
  remember (skipn _ _) as l' eqn:E.
  pose proof (firstn_skipn (abs rb - abs lb) l') as HH2.
  rewrite <- HH2 at 1. rewrite app_nth1; auto. 
  rewrite firstn_length_le; try math. subst l'; rewrite skipn_length; math.
Qed.

Corollary list_interval_nth' (def : A) (x lb rb : int) l :
  0 <= lb -> rb <= length l -> lb <= x < rb ->
  nth (abs (x - lb)) (list_interval (abs lb) (abs rb) l) def = nth (abs x) l def.
Proof. intros. rewrite -list_interval_nth; try math. f_equal; math. Qed.

Lemma slice_fullE l : list_interval (abs 0) (abs (length l)) l = l.
Proof. 
  rewrite /list_interval. etransitivity. 2: apply firstn_all.
  simpl. f_equal. math.
Qed. 

Lemma in_interval_list l lb rb x :
  In x (list_interval lb rb l) -> In x l.
Proof.
  rewrite /list_interval. intros. 
  rewrite -(firstn_skipn lb l) in_app_iff. right.
  rewrite -(firstn_skipn (rb - lb)%nat (skipn lb l)) in_app_iff. tauto.
Qed.

End list_interval.

Section sorted_max.

Import Sorted.

Definition sorted (l : list int) : Prop :=
  forall (i j : int), 
    (0 <= i < length l) -> 
    (0 <= j < length l) -> 
    (i < j) -> l[i] < l[j].

(* TODO is fold_right good? *)
Definition max (l : list int) : int := 
  match l with
  | nil => (-1)%Z
  | x :: _ => fold_right Z.max x l
  end.

Fact fold_right_max_base_le (l : list int) (a : int) :
  a <= fold_right Z.max a l.
Proof. induction l; simpl; try math. Qed.

Fact fold_right_max_base_dup (l : list int) (a : int) :
  Z.max a (fold_right Z.max a l) = fold_right Z.max a l.
Proof. induction l; simpl; try math. Qed.

Fact fold_right_max_base_change (l : list int) (a b : int) :
  Z.max a (fold_right Z.max b l) = Z.max b (fold_right Z.max a l).
Proof. induction l; simpl; try math. Qed.

Fact fold_right_max_base_change' (l : list int) (a b : int) :
  (fold_right Z.max a (b :: l)) = (fold_right Z.max b (a :: l)).
Proof. simpl. by rewrite fold_right_max_base_change. Qed.

Fact fold_right_max_basele_le (l : list int) (a b : int) (H : a <= b) :
  fold_right Z.max a l <= fold_right Z.max b l.
Proof. induction l; simpl; try math. Qed.

Fact fold_right_max_app (l l' : list int) (a : int) :
  fold_right Z.max a (List.app l l') = Z.max (fold_right Z.max a l) (fold_right Z.max a l').
Proof. induction l; simpl; try math. by rewrite fold_right_max_base_dup. Qed.

Fact fold_right_max_appr_le (l l' : list int) (a : int) :
  fold_right Z.max a l <= fold_right Z.max a (List.app l l').
Proof. rewrite fold_right_max_app. math. Qed.

Fact fold_right_max_appl_le (l l' : list int) (a : int) :
  fold_right Z.max a l <= fold_right Z.max a (List.app l' l).
Proof. rewrite fold_right_max_app. math. Qed.

Fact sorted_cons l x : sorted (x :: l) -> sorted l.
Proof.
  intros H. rewrite /sorted /= in H |- *. intros.
  specialize (H (i+1) (j+1)).
  replace (abs (i + 1)) with (S (abs i)) in H by math.
  replace (abs (j + 1)) with (S (abs j)) in H by math.
  apply H; math.
Qed.

Fact sorted_StronglySorted l : sorted l <-> StronglySorted Z.lt l.
Proof.
  induction l as [ | x l IH ].
  { rewrite /sorted /=. split; intros; try math. constructor. }
  { split; intros.
    { constructor. 
      { eapply IH, sorted_cons. apply H. }  
      { apply Forall_nth=> i d HH.
        rewrite -> nth_indep with (d':=0) by math.
        replace (nth i l 0) with (nth (S i) (x :: l) 0) by reflexivity.
        replace x with (nth 0%nat (x :: l) d) at 1 by reflexivity.
        rewrite -> nth_indep with (d':=0) by (simpl; math).
        replace 0%nat with (abs 0) by math. replace (S i) with (abs (i + 1)) by math.
        apply H; simpl; math. } }
    { apply StronglySorted_inv in H. destruct H as (H%IH & H0).
      hnf. simpl. intros.
      replace (abs j) with (S (abs (j - 1))) by math.
      case (classicT (i = 0))=> [ -> | Hneq ].
      { simpl. rewrite Forall_nth in H0. apply H0. math. }
      { assert (0 < i) by math. 
        replace (abs i) with (S (abs (i - 1))) by math.
        apply H; math. } } }
Qed.

Lemma sorted_nodup l : sorted l -> NoDup l.
Proof.
  intros H%sorted_StronglySorted. induction H; constructor.
  { intros HH. rewrite Forall_forall in H0. apply H0 in HH. math. }
  { auto. }
Qed.

Lemma max_le x l : 
  In x l -> x <= max l.
Proof. 
  induction l; simpl; intros; try contradiction. 
  destruct H as [ <- | H ]; try math. destruct l as [ | y l ]. 1: destruct H.
  apply IHl in H. simpl in H.
  rewrite ?fold_right_max_base_dup in H |- *. rewrite fold_right_max_base_change'. 
  etransitivity. apply H. change (a :: l) with (List.app (a :: nil) l). apply fold_right_max_appl_le.
Qed.

Fact max_cond l x (H : l <> nil) :
  x = max l <-> (forall y, In y l -> y <= x) /\ In x l.
Proof.
  revert x. induction l; simpl; intros; try contradiction.
  case (classicT (l = nil))=> [ -> | Hneq ].
  { simpl. rewrite Z.max_id. clear IHl. firstorder. math. }
  { pose proof (IHl Hneq) as HH. destruct l as [ | y l ]; try contradiction.
    rewrite fold_right_max_base_dup fold_right_max_base_change'.
    simpl in HH |- *. rewrite fold_right_max_base_dup in HH.
    epose proof (@eq_refl int _) as HR. rewrite -> HH in HR.
    split.
    { intros ->. split.
      { intros. destruct H0; try math. apply HR in H0. math. }
      { case (classicT (a = Z.max a (fold_right Z.max y l)))=> [ ? | Hneq2 ]; auto.
        have Hlt : Z.max a (fold_right Z.max y l) = (fold_right Z.max y l) by math.
        rewrite !Hlt. right. apply HR. } }
    { intros (H1 & H2). 
      pose proof (H1 _ (or_introl eq_refl)) as HH1. 
      pose proof (H1 _ (or_intror (or_introl eq_refl))) as HH2.
      destruct HR as (HR1 & HR2), H2 as [ -> | ].
      { destruct HR2; try math. assert (fold_right Z.max y l <= x) by (apply H1; auto). math. }
      { enough (x <= fold_right Z.max y l /\ fold_right Z.max y l <= x) by math.
        split; [ now apply HR1 | apply H1 ]. now right. } } }
Qed.

Fact max_upperbound_lt l (H : 0 < length l) q :
  (forall y, In y l -> y < q) -> max l < q.
Proof.
  case (classicT (l = nil))=>[ El | Hneq ]. 1: subst l; simpl in H; math.
  epose proof (@eq_refl int _) as H'. rewrite -> max_cond in H'. 2: apply Hneq.
  intros. destruct H' as (_ & H'). by apply H0 in H'.
Qed.

Lemma sorted_le i j l :
  sorted l ->
  0 <= i < length l ->
  0 <= j < length l ->
    i < j -> l[i] < l[j].
Proof. unfold sorted. auto. Qed.

Lemma sorted_leq i j l :
  sorted l ->
  0 <= i < length l ->
  0 <= j < length l ->
    i <= j -> l[i] <= l[j].
Proof. 
  intros H. intros. destruct (Z.eqb i j) eqn:E.
  { rewrite -> Z.eqb_eq in E. subst i. reflexivity. }
  { rewrite -> Z.eqb_neq in E. assert (i < j) by math.
    match goal with |- (?a <= ?b) => enough (a < b); try math end. 
    apply H; math. }
Qed.

Lemma sorted_le_rev i j l :
  sorted l ->
  0 <= i < length l ->
  0 <= j < length l ->
    l[i] < l[j] -> i < j.
Proof. 
  intros. case (classicT (i < j))=> [ | Hge ] //. have Hq : j <= i by math.
  enough (l[j] <= l[i]) by math. revert Hq. now apply sorted_leq. 
Qed.

Lemma sorted_app_l l1 l2 : sorted (List.app l1 l2) -> sorted l1.
Proof.
  intros. hnf in H |- *.
  intros. rewrite app_length in H.
  have Ha : 0 <= i < (length l1 + length l2)%nat by math.
  have Hb : 0 <= j < (length l1 + length l2)%nat by math.
  specialize (H _ _ Ha Hb H2).
  rewrite !app_nth1 in H; auto; math.
Qed.

Lemma sorted_app_r l1 l2 : sorted (List.app l1 l2) -> sorted l2.
Proof.
  intros. hnf in H |- *.
  intros. rewrite app_length in H.
  have Ha : 0 <= i + length l1 < (length l1 + length l2)%nat by math.
  have Hb : 0 <= j + length l1 < (length l1 + length l2)%nat by math.
  have HH : i + length l1 < j + length l1 by math.
  specialize (H _ _ Ha Hb HH).
  rewrite !app_nth2 in H; auto; try math.
  replace (abs (i + _) - _)%nat with (abs i) in H by math.
  replace (abs (j + _) - _)%nat with (abs j) in H by math. auto.
Qed.

Lemma sorted_app_lt l1 l2 : sorted (List.app l1 l2) -> 
  forall x y, In x l1 -> In y l2 -> x < y.
Proof.
  intros. apply In_nth_int in H0, H1.
  destruct H0 as (i & Hi & <-), H1 as (j & Hj & <-).
  hnf in H. rewrite app_length in H.
  have Ha : 0 <= i < (length l1 + length l2)%nat by math.
  have Hb : 0 <= j + length l1 < (length l1 + length l2)%nat by math.
  have HH : i < j + length l1 by math.
  specialize (H _ _ Ha Hb HH).
  rewrite -> app_nth1 in H at 1. 2: math.
  rewrite -> app_nth2 in H at 1. 2: math.
  eapply eq_ind_r with (y:=l2[j]). 1: apply H. f_equal. math.
Qed.

Fact sorted_bounded_sublist (l : list int) (Hs : sorted l) (M : int) (Hb : forall x, List.In x l -> 0 <= x < M) :
  l = List.filter (fun x => isTrue (List.In x l)) (lof id M).
Proof.
  revert M Hb. induction l as [ | x l IH ] using rev_ind; intros.
  { simpl. rewrite filter_all_false //. intros. exact isTrue_False. }
  { setoid_rewrite in_app_iff in Hb. simpl in Hb.
    pose proof (firstn_skipn (abs x) (lof id M)).
    rewrite -H. rewrite filter_app.
    pose proof (Hb _ (or_intror (or_introl eq_refl))) as Hx.
    rewrite -> IH with (M:=x).
    { f_equal.
      { replace (firstn _ _) with (lof id x).
        { apply filter_ext_in. intros a H0%In_lof_id. 
          rewrite isTrue_eq_isTrue_eq in_app_iff filter_In In_lof_id isTrue_eq_true_eq /=.
          intuition. }
        apply (nth_ext _ _ 0 0).
        { rewrite firstn_length_le ?length_lof' //. math. }
        { intros ?. rewrite length_lof'. intros.
          rewrite nth_firstn //.
          replace n with (abs n) by math.
          rewrite ?nth_lof; try math; auto. } }
      { pose proof (skipn_length (abs x) (lof id M)) as Hlen.
        rewrite length_lof' in Hlen. 
        rewrite -> filter_ext_in with (g:=fun x0 => isTrue (x = x0)).
        { remember (skipn (abs x) (lof id M)) as ll eqn:E. destruct ll. 1: simpl in Hlen; math. simpl.
          assert (x = z) as <-.
          { replace z with (skipn (abs x) (lof id M))[0] by now rewrite -E.
            rewrite nth_skipn. 2: rewrite length_lof'; try math.
            rewrite nth_lof; try math. }
          case_if. f_equal.
          rewrite filter_all_false //.
          intros. rewrite isTrue_eq_false_eq. 
          apply In_nth_int in H0. destruct H0 as (i & Hi & <-).
          destruct ll eqn:EE; simpl in Hi, Hlen; try math.
          rewrite <- ! EE in *.
          assert (ll = skipn (1 + (abs x))%nat (lof id M)) as ->.
          { rewrite -skipn_skipn -E //. }
          rewrite nth_skipn ?nth_lof ?length_lof'; try math.
          replace (abs i + (1 + abs x))%nat with (abs (x + i + 1))%nat by math.
          rewrite nth_lof; math. }
        { intros. rewrite isTrue_eq_isTrue_eq in_app_iff filter_In In_lof_id isTrue_eq_true_eq /=.
          apply In_nth_int in H0. destruct H0 as (i & Hi & <-).
          rewrite Hlen in Hi.
          rewrite nth_skipn ?nth_lof ?length_lof'; try math.
          replace (abs i + abs x)%nat with (abs (i+x)) by math.
          rewrite ?nth_lof'; try math. intuition math. } } }
    { hnf in Hs |- *. intros.
      replace l[i] with (List.app l (x :: nil))[i].
      1: replace l[j] with (List.app l (x :: nil))[j].
      2-3: rewrite app_nth1; try math.
      apply Hs; rewrite ?app_length /=; math. }
    { intros. split. 1: apply Hb; auto.
      apply In_nth_int in H0. destruct H0 as (i & Hi & <-).
      replace x with (List.app l (x :: nil))[length l].
      2: rewrite app_nth2; try math.
      2: replace (abs _ - _)%nat with 0%nat; auto; math.
      replace l[i] with (List.app l (x :: nil))[i].
      2: rewrite app_nth1; try math.
      apply Hs; rewrite ?app_length /=; math. } }
Qed.

Lemma sorted_max_size l i (Hi : 0 <= i) : 
  sorted l -> i + 1 = length l -> l[i] = max l.
Proof. 
  intros. apply max_cond. 1: destruct l; simpl in *; math. split.
  { intros. apply In_nth_int in H1. destruct H1 as (j & Hj & <-).
    apply sorted_leq; try math; auto. }
  { apply nth_In_int. math. }
Qed. 

Lemma sorted_last_max l def (H : l <> nil) : 
  sorted l -> last l def = max l.
Proof.
  intros. 
  have HH : 0 <= length l - 1.
  { destruct l; try contradiction. simpl length. lia. }
  rewrite -(sorted_max_size (i:=(length l - 1)%Z)) //; try math.
  rewrite -(nth_last 0 def) //. f_equal. math.
Qed.

Lemma nth_le_max l i :
  0 <= i < length l ->
  sorted l ->
  l[i] >= max l -> i + 1 = length l.
Proof.
  intros. case (classicT (i + 1 = Datatypes.length l))=> [ | Hneq ]; auto.
  have Hlt : i < length l - 1 by math.
  rewrite <- sorted_max_size with (i:=length l - 1) in H1; try math; auto.
  eapply sorted_le in Hlt; eauto. all: math.
Qed.

Lemma max_takeS i l : 
  0 <= i < length l -> 0 <= l[i] ->
  max (take (abs (i + 1)) l) = Z.max l[i] (max (take (abs i) l)).
Proof. 
  rewrite !take_conversion.
  intros. assert (length (firstn (abs (i+1)) l) = abs (i+1)) as Hlen by (rewrite firstn_length_le; math).
  case (classicT ((firstn (abs (i + 1)) l) = nil)); [ intros C; rewrite C in Hlen | intros (l' & a & E)%exists_last ]; 
    simpl in Hlen; try math.
  pose proof (@removelast_firstn _ (abs i) l ltac:(math)) as Hq.
  replace (S (abs i)) with (abs (i+1)) in Hq by math. rewrite E removelast_last in Hq. subst l'.
  assert (a = l[i]) as ->.
  { replace a with (firstn (abs (i + 1)) l)[i].
    { rewrite nth_firstn; math. }
    rewrite E app_nth2 ?firstn_length_le; try math. replace (abs i - abs i)%nat with 0%nat by math. auto. }
  rewrite E. destruct (firstn _ _) in |- *; simpl; rewrite ?fold_right_max_app /=; try math.
Qed.

Lemma In_lt x i l :
  0 <= i < length l - 1 ->
  sorted l -> In x l -> x < l[i+1] -> x <= l[i].
Proof. 
  intros. apply In_nth_int in H1. destruct H1 as (j & Hj & <-). 
  apply sorted_le_rev in H2; try math; auto. apply sorted_leq; try math; auto.
Qed.

Lemma max_sublist l1 l2 (Hlen : 0 < length l1) :
  (forall x, In x l1 -> In x l2) -> max l2 >= max l1.
Proof.
  have H1 : l1 <> nil by destruct l1; simpl in Hlen; try lia.
  intros.
  have H2 : l2 <> nil by destruct l1 as [ | x l1 ]; try contradiction; destruct l2; auto; specialize (H _ (or_introl eq_refl)); simpl in H.
  epose proof (@eq_refl int _) as H1'. rewrite -> max_cond in H1'. 2: apply H1.
  epose proof (@eq_refl int _) as H2'. rewrite -> max_cond in H2'. 2: apply H2.
  pose proof (proj1 H2' _ (H _ (proj2 H1'))). math.
Qed.

Lemma max0 : max nil = -1.
Proof. reflexivity. Qed.

Lemma In_le_0 l x :
  sorted l -> In x l -> x >= l[0].
Proof. 
  intros. apply In_nth_int in H0. enough (l[0] <= x) by math. 
  destruct H0 as (i & Hi & <-). apply sorted_leq; try math; auto. 
Qed.

End sorted_max.

Section merge.

Import Sorted.

(*
Definition merge' (l1 l2 : list int) (f : list int -> list int -> list int) : list int :=
  match l1, l2 with
  | x :: l1', y :: l2' => 
    If x = y 
    then x :: (f l1' l2') 
    else (If x < y then x :: (f l1' l2) else y :: (f l1 l2'))
  | _ :: _, nil => l1
  | nil, _ => l2
  end.
*)
Fixpoint merge (l1 l2 : list int) : list int :=
  let fix merge_aux (l2 : list int) : list int :=
  match l1, l2 with
  | x :: l1', y :: l2' => 
    If x = y 
    then x :: (merge l1' l2') 
    else (If x < y then x :: (merge l1' l2) else y :: (merge_aux l2'))
  | _ :: _, nil => l1
  | nil, _ => l2
  end in merge_aux l2.

Fact merge_nil_l l : merge nil l = l.
Proof. destruct l; auto. Qed.

Fact merge_nil_r l : merge l nil = l.
Proof. destruct l; auto. Qed.

Lemma In_merge l1 l2 x : In x (merge l1 l2) = (In x l1 \/ In x l2).
Proof.
  extens. revert l2.
  induction l1 as [ | a l1 IH ]; intros; simpl.
  { destruct l2; simpl; tauto. }
  { induction l2 as [ | b l2 IH2 ]; intros; simpl.
    { tauto. }
    { case_if. 
      { simpl. rewrite IH. subst a. tauto. }
      { case_if.
        { simpl. rewrite IH. simpl. tauto. }
        { simpl. rewrite IH2. tauto. } } } }
Qed.

Lemma sorted_merge l1 l2 : sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  rewrite !sorted_StronglySorted.
  revert l2. induction l1 as [ | x l1 IH ]; intros; simpl.
  { destruct l2; simpl; assumption. }
  { induction l2 as [ | y l2 IH2 ]; intros; simpl.
    { assumption. }
    { case_if. 
      { subst x. apply StronglySorted_inv in H, H0. destruct H, H0.
        constructor. 1: apply IH; tauto.
        rewrite -> Forall_forall in *. intros x. rewrite In_merge.
        intros [ | ]; auto. }
      { case_if.
        { apply StronglySorted_inv in H. constructor. 1: apply IH; tauto.
          apply StronglySorted_inv in H0. destruct H, H0.
          rewrite -> Forall_forall in *. intros z. rewrite In_merge.
          simpl. intros [ | [ -> | ] ]; auto. transitivity y; auto. }
        { rewrite -/(merge (x :: l1) l2). have CC : y < x by math.
          apply StronglySorted_inv in H0. specialize (IH2 (proj1 H0)). constructor; auto.
          apply StronglySorted_inv in H. destruct H, H0.
          rewrite -> Forall_forall in *. intros z. rewrite In_merge.
          simpl. intros [ [ -> | ] | ]; auto. transitivity x; auto. } } } }
Qed.

Lemma size_merge l1 l2: 
  length (merge l1 l2) >= Z.max (length l1) (length l2).
Proof.
  revert l2.
  induction l1 as [ | a l1 IH ]; intros; simpl.
  { destruct l2; simpl; math. }
  { induction l2 as [ | b l2 IH2 ]; intros; simpl.
    { math. }
    { case_if. 
      { simpl. specialize (IH l2). math. }
      { case_if; simpl.
        { specialize (IH (b :: l2)). simpl in IH. math. }
        { rewrite -?/(merge (_ :: l1) l2) in IH2 |- *; try math. } } } }
Qed.

Lemma merge_nth0 l1 l2 :
  length l1 > 0 ->
  length l2 > 0 ->
  (merge l1 l2)[0] = Z.min l1[0] l2[0].
Proof.
  destruct l1, l2; simpl; try math. move=> _ _.
  case_if; simpl; try math. case_if; simpl; try math.
Qed. 

Lemma max_merge l1 l2 : 
  l1 <> nil ->
  l2 <> nil ->
  sorted l1 -> 
  sorted l2 ->
    max (merge l1 l2) = Z.max (max l1) (max l2).
Proof. 
  intros. symmetry. apply max_cond.
  { destruct l1, l2; try contradiction; simpl; do 2 (try case_if; try discriminate). }
  { epose proof (@eq_refl int _) as HH1. rewrite -> (max_cond (l:=l1)) in HH1; auto.
    epose proof (@eq_refl int _) as HH2. rewrite -> (max_cond (l:=l2)) in HH2; auto.
    split.
    { intros. rewrite In_merge in H3. destruct H3; [ apply HH1 in H3 | apply HH2 in H3 ]; math. }
    { destruct (Z.max_spec_le (max l1) (max l2)) as [ (_ & ->) | (_ & ->) ].
      all: rewrite In_merge; tauto. } }
Qed.

Lemma max_merge_last_ge1 l1 l2 def : 
  l1 <> nil ->
  sorted l1 -> 
  sorted l2 ->
    last (merge l1 l2) def >= last l1 def.
Proof.
  intros.
  assert (0 < length l1) as Hq by (destruct l1; try contradiction; simpl; math).
  pose proof (size_merge l1 l2) as HH.
  assert (merge l1 l2 <> nil) as Hq2 by (destruct (merge l1 l2); simpl in HH; auto; math).
  rewrite !sorted_last_max //. 
  2: apply sorted_merge; auto.
  case (classicT (l2 = nil))=> [ -> | Hneq ].
  { rewrite merge_nil_r. math. }
  { enough (max (merge l1 l2) = Z.max (max l1) (max l2)) by math. by apply max_merge. }
Qed.

Lemma max_merge_last_ge2 l1 l2 def : 
  l2 <> nil ->
  sorted l1 -> 
  sorted l2 ->
    last (merge l1 l2) def >= last l2 def.
Proof.
  intros.
  assert (0 < length l2) as Hq by (destruct l2; try contradiction; simpl; math).
  pose proof (size_merge l1 l2) as HH.
  assert (merge l1 l2 <> nil) as Hq2 by (destruct (merge l1 l2); simpl in HH; auto; math).
  rewrite !sorted_last_max //. 
  2: apply sorted_merge; auto.
  case (classicT (l1 = nil))=> [ -> | Hneq ].
  { rewrite merge_nil_l. math. }
  { enough (max (merge l1 l2) = Z.max (max l1) (max l2)) by math. by apply max_merge. }
Qed.

Lemma merge_split (n : nat) : forall l1 l2 (H : (n <= length (merge l1 l2))%nat)
  (Hs1 : StronglySorted Z.lt l1) (Hs2 : StronglySorted Z.lt l2),
  exists pre1 suf1 pre2 suf2, 
    l1 = pre1 ++ suf1 /\
    l2 = pre2 ++ suf2 /\
    (firstn n (merge l1 l2)) = merge pre1 pre2 /\
    (skipn n (merge l1 l2)) = merge suf1 suf2 /\
    (pre1 <> nil -> suf2 <> nil -> last pre1 0 <> hd 0 suf2) /\
    (pre2 <> nil -> suf1 <> nil -> last pre2 0 <> hd 0 suf1).
Proof.
  induction n as [ | n IH ]; intros.
  { exists (@nil int), l1, (@nil int), l2. do 4 (split; auto). }
  { destruct l1 as [ | a l1 ].
    { destruct l2 as [ | b l2 ].
      1: simpl in H; math.
      rewrite merge_nil_l in H. simpl in H. apply le_S_n in H.
      specialize (IH nil l2). rewrite merge_nil_l in IH.
      specialize (IH H).
      apply StronglySorted_inv in Hs2. destruct Hs2 as (Hs2 & Hnotin). specialize (IH Hs1 Hs2).
      destruct IH as (pre1 & suf1 & pre2 & suf2 & Enn & -> & Hfirst & Hskip & _ & Hgood2).
      destruct suf1. 2: exfalso; revert Enn; apply app_cons_not_nil.
      destruct pre1; try discriminate.
      rewrite app_comm_cons.
      exists (@nil int), (@nil int), (b :: pre2), suf2.
      do 2 (split; auto). 
      rewrite -> merge_nil_l in *. rewrite !merge_nil_l. 
      simpl. rewrite Hfirst Hskip. do 3 (split; auto). }
    { destruct l2 as [ | b l2 ].
      { rewrite merge_nil_r in H. simpl in H. apply le_S_n in H.
        specialize (IH l1 nil). rewrite merge_nil_r in IH.
        specialize (IH H).
        apply StronglySorted_inv in Hs1. destruct Hs1 as (Hs1 & Hnotin). specialize (IH Hs1 Hs2).
        destruct IH as (pre1 & suf1 & pre2 & suf2 & -> & Enn & Hfirst & Hskip & Hgood1 & _).
        destruct suf2. 2: exfalso; revert Enn; apply app_cons_not_nil.
        destruct pre2; try discriminate.
        rewrite app_comm_cons.
        exists (a :: pre1), suf1, (@nil int), (@nil int).
        do 2 (split; auto). 
        rewrite -> merge_nil_r in *. rewrite !merge_nil_r. 
        simpl. rewrite Hfirst Hskip. do 3 (split; auto). }
      { simpl in H. case_if.
        { subst a.
          simpl in H. apply le_S_n in H.
          specialize (IH _ _ H (proj1 (StronglySorted_inv Hs1)) (proj1 (StronglySorted_inv Hs2))).
          apply sorted_StronglySorted, sorted_nodup, NoDup_cons_iff in Hs1, Hs2. 
          destruct Hs1 as (Hnotin1 & Hs1), Hs2 as (Hnotin2 & Hs2).
          destruct IH as (pre1 & suf1 & pre2 & suf2 & -> & -> & Hfirst & Hskip & Hgood1 & Hgood2).
          rewrite !in_app_iff in Hnotin1, Hnotin2.
          rewrite !app_comm_cons.
          do 4 eexists. do 2 (split; [ reflexivity | ]).
          rewrite -!app_comm_cons. 
          simpl merge. simpl firstn. simpl skipn. case_if.
          rewrite Hfirst Hskip. do 2 (split; auto).
          split=> Ha Hb.
          { destruct pre1. 
            { simpl. destruct suf2 as [ | yy ? ]; try contradiction.
              simpl in Hnotin2 |- *. intros ->; apply Hnotin2; tauto. }
            { rewrite -> 1 last_notnil. 2: discriminate.
              apply Hgood1; auto; discriminate. } }
          { destruct pre2. 
            { simpl. destruct suf1 as [ | yy ? ]; try contradiction.
              simpl in Hnotin1 |- *. intros ->; apply Hnotin1; tauto. }
            { rewrite -> 1 last_notnil. 2: discriminate.
              apply Hgood2; auto; discriminate. } } }
        { case_if.
          { simpl length in H. apply le_S_n in H.
            specialize (IH _ _ H (proj1 (StronglySorted_inv Hs1)) Hs2).
            apply StronglySorted_inv in Hs2.
            destruct Hs2 as (_ & Hnotin2). rewrite Forall_forall in Hnotin2.
            destruct IH as (pre1 & suf1 & pre2 & suf2 & -> & E2 & Hfirst & Hskip & Hgood1 & Hgood2).
            rewrite !app_comm_cons.
            do 4 eexists. rewrite -> E2 at 1. do 2 (split; [ reflexivity | ]).
            rewrite -!app_comm_cons.
            simpl merge. case_if. case_if. simpl firstn. simpl skipn.
            rewrite Hfirst Hskip.
            rewrite -/(merge (a :: pre1) pre2). split. 2: split; auto.
            { destruct pre2.
              1: by rewrite !merge_nil_r.
              rewrite -app_comm_cons in E2. assert (b = z) as <- by congruence.
              simpl. case_if. case_if. auto. }
            split; auto. intros Ha Hb.
            destruct pre1.
            { simpl. destruct suf2 as [ | yy ? ]; try contradiction.
              simpl. intros ->. 
              destruct pre2. 1: simpl in E2; congruence.
              simpl in E2. inversion E2. subst b l2.
              specialize (Hnotin2 yy). rewrite in_app_iff /= in Hnotin2.
              enough (z < yy) by math. apply Hnotin2. auto. }
            { rewrite -> 1 last_notnil. 2: discriminate.
              apply Hgood1; auto; discriminate. } }
          { simpl length in H. apply le_S_n in H.
            rewrite -/(merge (a :: l1) l2) in H. 
            specialize (IH _ _ H Hs1 (proj1 (StronglySorted_inv Hs2))).
            apply StronglySorted_inv in Hs1.
            destruct Hs1 as (_ & Hnotin1). rewrite Forall_forall in Hnotin1.
            destruct IH as (pre1 & suf1 & pre2 & suf2 & E1 & -> & Hfirst & Hskip & Hgood1 & Hgood2).
            rewrite !app_comm_cons.
            do 4 eexists. rewrite -> E1 at 1. do 2 (split; [ reflexivity | ]).
            rewrite -!app_comm_cons.
            simpl merge. case_if. case_if. simpl firstn. simpl skipn.
            rewrite Hfirst Hskip.
            split. 2: split; auto.
            { destruct pre1.
              1: by rewrite !merge_nil_l.
              rewrite -app_comm_cons in E1. assert (a = z) as <- by congruence.
              simpl. case_if. case_if. auto. }
            split; auto. intros Ha Hb.
            destruct pre2.
            { simpl. destruct suf1 as [ | yy ? ]; try contradiction.
              simpl. intros ->. 
              destruct pre1. 1: simpl in E1; congruence.
              simpl in E1. inversion E1. subst a l1.
              specialize (Hnotin1 yy). rewrite in_app_iff /= in Hnotin1.
              enough (z < yy) by math. apply Hnotin1. auto. }
            { rewrite -> 1 last_notnil. 2: discriminate.
              apply Hgood2; auto; discriminate. } } } } } }
Qed.

End merge.

Section search_leastupperbound.

(* TODO compare with the sigT search function below? *)
Definition search_core (x : int) (l : list int) := find (Z.ltb x) l.

Fact search_core_neccond x l (H : sorted l) y :
  search_core x l = Some y -> 
    exists i, 0 <= i < length l /\ y = l[i] /\ x < y /\
      (forall j, 0 <= j < i -> l[j] <= x).
Proof.
  revert y. rewrite /search_core. induction l as [ | q l IH ]; intros; simpl; try discriminate.
  simpl in H0. destruct (Z.ltb x q) eqn:E.
  { injection H0 as ->. apply Z.ltb_lt in E.
    exists 0. split; try math. simpl. do 2 (split; auto).
    intros. math. }
  { apply IH in H0. 2: eapply sorted_cons; eauto.
    destruct H0 as (i & Hi & -> & Hlt & HH).
    exists (i + 1). split; try math. replace (abs (i + 1)) with (S (abs i)) by math.
    do 2 (split; auto). intros. apply Z.ltb_ge in E.
    case (classicT (j = 0))=> [ -> | Hneq ] //.
    assert (0 < j) by math. 
    replace (abs j) with (S (abs (j - 1))) by math.
    apply HH; math. }
Qed.

Fact search_core_sufcond x l (H : sorted l) :
  forall i, 0 <= i < length l -> x < l[i] ->
    (forall j, 0 <= j < i -> l[j] <= x) -> 
    search_core x l = Some l[i].
Proof.
  induction l as [ | q l IH ]; simpl; intros; try math.
  specialize (IH (sorted_cons H)).
  destruct (Z.ltb x q) eqn:E.
  { apply Z.ltb_lt in E. f_equal.
    enough (i = 0) by (subst i; reflexivity).
    case (classicT (i = 0))=> [ | Hneq ] //.
    assert (0 <= 0 < i) as Htmp by math.
    specialize (H2 0 Htmp). simpl in H2. math. }
  { apply Z.ltb_ge in E.
    case (classicT (i = 0))=> [ ? | Hneq ].  
    1: subst i; simpl in H1; try math.
    assert (0 < i) as Htmp by math.
    replace (abs i) with (S (abs (i-1))) in H1 |- * by math.
    apply IH; try math. intros.
    assert (0 <= j + 1 < i) as Htmp2 by math.
    apply H2 in Htmp2. replace (abs (j + 1)) with (S (abs j)) in Htmp2 by math. auto. }
Qed.

Variable (def : int).

Definition search (x : int) (l : list int) : int :=
  match search_core x l with
  | Some y => y
  | None => def
  end.

Fact search_sufcond l x y : search_core l x = Some y -> search l x = y.
Proof. unfold search. now intros ->. Qed.

Lemma search_lt_nth l i x : 
  sorted l -> 
  0 <= i < length l ->
    (forall y, In y l -> y < l[i] -> y <= x) ->
    x < l[i] ->
    search x l = l[i].
Proof.
  intros. apply search_sufcond, search_core_sufcond; auto.
  intros. apply H1. 1: apply nth_In_int; math. apply sorted_le; try math; auto.
Qed.

Lemma search_nth l i : 
  sorted l -> 
  0 < i + 1 < length l ->
    search l[i] l = l[i + 1].
Proof.
  intros. apply search_sufcond, search_core_sufcond; auto; try math.
  1: apply sorted_le; try math; auto. 
  intros. apply sorted_leq; try math; auto.
Qed. 

Lemma search_nth_pred l i x : 
  sorted l -> 
  0 < i < length l ->
    l[i-1] <= x < l[i] ->
    search x l = l[i].
Proof.
  intros. apply search_sufcond, search_core_sufcond; auto; try math.
  intros. etransitivity. 2: apply H1. apply sorted_leq; try math; auto.
Qed.

Lemma search_nth_pred' l i x : 
  sorted l -> 
  0 < i < length l ->
    l[i-1] <= x < l[i] ->
    search_core x l = Some l[i].
Proof.
  intros. apply search_core_sufcond; auto; try math.
  intros. etransitivity. 2: apply H1. apply sorted_leq; try math; auto.
Qed.

Lemma merge_nthS l1 l2 i (Hnotnil1 : l1 <> nil) (Hnotnil2 : l2 <> nil) 
  (Hm1 : max l1 <= def) (Hm2 : max l2 <= def) :
  sorted l1 -> sorted l2 ->
  0 < i + 1 < length (merge l1 l2) ->
    (merge l1 l2)[i+1] = Z.min (search (merge l1 l2)[i] l1) (search (merge l1 l2)[i] l2).
Proof.
  intros. pose proof H as HH%sorted_StronglySorted. pose proof H0 as HH0%sorted_StronglySorted.
  assert (sorted (merge l1 l2)) as Hsom by now apply sorted_merge.
  have Hle : ((abs (i + 1)) <= length (merge l1 l2))%nat by math.
  pose proof (merge_split Hle HH HH0) as (pre1 & suf1 & pre2 & suf2 & E1 & E2 & Hfirst & Hskip & Hgood1 & Hgood2).
  replace (abs (i+1)) with (0 + (abs (i+1)))%nat by math.
  rewrite <- nth_skipn with (l:=merge l1 l2); try lia. rewrite Hskip.
  assert (length (merge pre1 pre2) = abs (i + 1) :> nat) as Hgt.
  1: rewrite -Hfirst firstn_length_le; math.
  pose proof Hgt as Hgt'. rewrite -Hfirst in Hgt.
  replace (abs i) with (length (firstn (abs (i + 1)) (merge l1 l2)) - 1)%nat; try lia.
  rewrite <- (nth_firstn (merge l1 l2)) with (n:=abs (i+1)); try lia.
  rewrite Hfirst (nth_last _ 0). 2: destruct (merge pre1 pre2); simpl in Hgt'; try discriminate; try math.
  pose proof H as Hsp1. rewrite E1 in Hsp1. pose proof Hsp1 as Hss1%sorted_app_r. apply sorted_app_l in Hsp1.
  pose proof H0 as Hsp2. rewrite E2 in Hsp2. pose proof Hsp2 as Hss2%sorted_app_r. apply sorted_app_l in Hsp2.
  assert (length (merge suf1 suf2) > 0) as Hgt0.
  { rewrite -Hskip skipn_length. math. }
  assert (pre1 <> nil -> last (merge pre1 pre2) 0 >= last pre1 0) as HH1.
  { intros Hq. apply max_merge_last_ge1; auto. }
  assert (pre2 <> nil -> last (merge pre1 pre2) 0 >= last pre2 0) as HH2.
  { intros Hq. apply max_merge_last_ge2; auto. }
  pose proof (firstn_skipn (abs (i + 1)) (merge l1 l2)) as Htmp.
  match type of Htmp with (List.app ?ll1 ?ll2) = _ => 
    pose proof (sorted_app_lt ll1 ll2) as Htmp2 end.
  rewrite Htmp Hfirst Hskip in Htmp2. specialize (Htmp2 Hsom).
  setoid_rewrite In_merge in Htmp2.

  assert (match suf1 with
    | nil => search (last (merge pre1 pre2) 0) l1 = def
    | x :: _ => search_core (last (merge pre1 pre2) 0) l1 = Some x
    end) as Hq1.
  { destruct suf1 as [ | x suf1 ].
    { rewrite app_nil_r in E1. subst l1.
      case (classicT (pre1 = nil))=> [ -> | Hneq ] //.
      pose proof Hneq as Hneq'.
      apply HH1 in Hneq; auto.
      unfold search. destruct (search_core _ _) eqn:E; auto.
      apply find_some in E. rewrite Z.ltb_lt in E.
      pose proof Hneq' as Hneq''.
      apply sorted_last_max with (def:=0) in Hneq'; auto. rewrite max_cond // in Hneq'.
      destruct E as (E & Hlt). apply Hneq' in E. math. }
    { case (classicT (pre1 = nil))=> [ El1 | Hneq ].
      { subst pre1 l1. rewrite merge_nil_l.
        simpl. unfold search. simpl.
        case (classicT (pre2 = nil))=> [ El2 | Hneq2 ].
        1: subst pre2; simpl in Hgt'; math.
        apply exists_last in Hneq2. destruct Hneq2 as (pre2' & lst & ->).
        rewrite last_last.
        specialize (Htmp2 lst x). rewrite in_app_iff /= in Htmp2. 
        assert (lst < x) as Hltt%Z.ltb_lt by (apply Htmp2; auto). now rewrite Hltt. }
      { assert (x = l1[length pre1]) as ->.
        { rewrite E1. replace (abs _) with (length pre1) by math. by rewrite nth_middle. }
        assert (0 < length pre1) as HHH by (destruct pre1; try contradiction; simpl; math).
        apply search_nth_pred'; auto. 
        1: rewrite E1; rewrite app_length; simpl; math.
        split.
        { rewrite E1 app_nth1; try math. 
          replace (abs (length pre1 - 1)) with (length pre1 - 1)%nat by math. 
          rewrite -> nth_last with (b:=0); auto.
          apply HH1 in Hneq. math. }
        { apply (last_sufcond 0). 1: destruct (merge pre1 pre2); simpl in Hgt'; math.
          intros x. rewrite In_merge. intros. apply Htmp2; simpl; auto. } } } }

  assert (match suf2 with
    | nil => search (last (merge pre1 pre2) 0) l2 = def
    | x :: _ => search_core (last (merge pre1 pre2) 0) l2 = Some x
    end) as Hq2.
  { destruct suf2 as [ | x suf2 ].
    { rewrite app_nil_r in E2. subst l2.
      case (classicT (pre2 = nil))=> [ -> | Hneq ] //.
      pose proof Hneq as Hneq'.
      apply HH2 in Hneq; auto.
      unfold search. destruct (search_core _ _) eqn:E in |- *; auto.
      apply find_some in E. rewrite Z.ltb_lt in E.
      pose proof Hneq' as Hneq''.
      apply sorted_last_max with (def:=0) in Hneq'; auto. rewrite max_cond // in Hneq'.
      destruct E as (E & Hlt). apply Hneq' in E. math. }
    { case (classicT (pre2 = nil))=> [ El2 | Hneq ].
      { subst pre2 l2. rewrite merge_nil_r.
        simpl. unfold search. simpl.
        case (classicT (pre1 = nil))=> [ El1 | Hneq1 ].
        1: subst pre1; simpl in Hgt'; math.
        apply exists_last in Hneq1. destruct Hneq1 as (pre1' & lst & ->).
        rewrite last_last.
        specialize (Htmp2 lst x). rewrite in_app_iff /= in Htmp2. 
        assert (lst < x) as Hltt%Z.ltb_lt by (apply Htmp2; auto). now rewrite Hltt. }
      { assert (x = l2[length pre2]) as ->.
        { rewrite E2. replace (abs _) with (length pre2) by math. by rewrite nth_middle. }
        assert (0 < length pre2) as HHH by (destruct pre2; try contradiction; simpl; math).
        apply search_nth_pred'; auto. 
        1: rewrite E2; rewrite app_length; simpl; math.
        split.
        { rewrite E2 app_nth1; try math. 
          replace (abs (length pre2 - 1)) with (length pre2 - 1)%nat by math. 
          rewrite -> nth_last with (b:=0); auto.
          apply HH2 in Hneq. math. }
        { apply (last_sufcond 0). 1: destruct (merge pre1 pre2); simpl in Hgt'; math.
          intros x. rewrite In_merge. intros. apply Htmp2; simpl; auto. } } } }

  destruct suf1 as [ | x suf1 ].
  { rewrite app_nil_r in E1. subst l1.
    destruct suf2 as [ | y suf2 ].
    1: simpl in Hgt0; math.
    rewrite merge_nil_l. simpl. unfold search at 2. rewrite Hq1 Hq2.
    pose proof Hnotnil1 as Hlst%HH1. rewrite (sorted_last_max (l:=pre1)) // in Hlst.
    apply find_some, proj1 in Hq2. 
    epose proof (@eq_refl int _) as Htmp3. rewrite -> (@max_cond l2) in Htmp3; auto.
    apply Htmp3 in Hq2. math. }
  { destruct suf2 as [ | y suf2 ].
    { rewrite app_nil_r in E2. subst l2.
      rewrite merge_nil_r. simpl. unfold search at 1. rewrite Hq1 Hq2.
      pose proof Hnotnil2 as Hlst%HH2. rewrite (sorted_last_max (l:=pre2)) // in Hlst.
      apply find_some, proj1 in Hq1. 
      epose proof (@eq_refl int _) as Htmp3. rewrite -> (@max_cond l1) in Htmp3; auto.
      apply Htmp3 in Hq1. math. }
    { replace 0%nat with (abs 0) by math. rewrite merge_nth0; simpl; try math.
      by rewrite /search Hq1 Hq2. } }
Qed.

End search_leastupperbound.

Section search_pure_facts.

Import List.

Class IncreasingIntList (L : list int) := {
  IIL_L_first : List.nth (abs 0) L 0 = 0;
  IIL_L_notnil : (0 < length L);
  IIL_L_inc : forall (i j : int), 
    (0 <= i < length L) -> 
    (0 <= j < length L) -> 
    (i < j) -> 
    (List.nth (abs i) L 0 < List.nth (abs j) L 0)
}.

Context (L : list int) {H : IncreasingIntList L}.

Fact IIL_L_inc' : forall (i j : int), 
  (0 <= i < length L) -> 
  (0 <= j < length L) -> 
  (i <= j) -> 
  (List.nth (abs i) L 0 <= List.nth (abs j) L 0).
Proof.
  intros. destruct (Z.eqb i j) eqn:E.
  { rewrite -> Z.eqb_eq in E. subst i. reflexivity. }
  { rewrite -> Z.eqb_neq in E. assert (i < j) by math.
    match goal with |- (?a <= ?b) => enough (a < b); try math end. 
    apply IIL_L_inc; math.
  }
Qed.
(*
Fact IIL_L_last : (abs (length L - 1)) = (abs (length L - 1)%nat).
Proof. pose proof IIL_L_notnil. math. Qed.

Hint Rewrite IIL_L_last : rew_maths.
*)
Variable (N : int).
Hypothesis H_L_last : List.nth (abs (length L - 1)) L 0 = N.  (* add abs to keep consistent *)

Fact IIL_zero_le_N : (0 <= N).
Proof.
  rewrite <- IIL_L_first, <- H_L_last.
  pose proof IIL_L_notnil.
  apply IIL_L_inc'; math.
Qed.

Fact IIL_L_bounded_impl (i a : int) 
  (Ha1 : (0 <= a < (length L - 1))) (Ha2 : (List.nth (abs a) L 0 <= i < List.nth (abs (a + 1)) L 0)) :
  0 <= i < N.
Proof.
  split.
  { transitivity (nth (abs a) L 0); try math.
    rewrite <- IIL_L_first at 1.
    apply IIL_L_inc'; math.
  }
  { enough (nth (abs (a + 1)) L 0 <= N) by math.
    subst N.
    apply IIL_L_inc'; math.
  }
Qed.

Fact search_exists j (Hj : (0 <= j < N)) :
  sig (fun a => (0 <= a < (length L - 1)) /\ (List.nth (abs a) L 0 <= j < List.nth (abs (a + 1)) L 0)).
Proof.
  destruct (Nat.leb (length L) 1) eqn:Ej.
  1:{ 
    apply Nat.leb_le in Ej. 
    pose proof IIL_L_notnil.
    assert (length L = 1%nat) as E by math.
    pose proof H_L_last as HH.
    rewrite E IIL_L_first in HH.
    math.
  }
  apply Nat.leb_gt in Ej.
  remember (abs j) as n eqn:En.
  revert j Hj En.
  induction n; intros.
  { assert (j = 0) as -> by math.
    exists 0. split; try math.
    split. 1: now rewrite IIL_L_first.
    rewrite <- IIL_L_first at 1.
    apply IIL_L_inc; math.
  }
  { assert (n = abs (j - 1)) as H1 by math.
    assert (0 <= j - 1 < N) as H2 by math.
    specialize (IHn _ H2 H1).
    destruct IHn as (a & Ha1 & Ha2).
    (* TODO relation with the imperative program? *)
    destruct (Z.leb (List.nth (abs (a + 1)) L 0) j) eqn:E.
    { apply Z.leb_le in E.
      assert (a + 1 < (length L - 1)) as Hlt.
      { destruct (Z.leb (length L - 1) (a + 1)) eqn:E'.
        2: apply Z.leb_gt in E'; math.
        apply Z.leb_le in E'.
        assert (a + 1 = (length L - 1)) as EE by math.
        rewrite EE in E.
        math.
      }
      assert (j = List.nth (abs (a + 1)) L 0) as -> by math.
      exists (a+1).
      split; [ math | split; [ math | apply IIL_L_inc; math ] ].
    }
    { apply Z.leb_gt in E.
      exists a.
      split; [ assumption | math ].
    }
  }
Qed.

Fact search_unify j (Hj : (0 <= j < N))
  a (Ha1 : (0 <= a < (length L - 1))) (Ha2 : (List.nth (abs a) L 0 <= j < List.nth (abs (a + 1)) L 0))
  a' (Ha1' : (0 <= a' < (length L - 1))) (Ha2' : (List.nth (abs a') L 0 <= j < List.nth (abs (a' + 1)) L 0)) :
  a = a'.
Proof.
  destruct (Z.leb (a'+1) a) eqn:Eu.
  { rewrite -> Z.leb_le in Eu.
    enough (List.nth (abs (a' + 1)) L 0 <= List.nth (abs a) L 0) by math.
    apply IIL_L_inc'; math.
  }
  { destruct (Z.leb (a+1) a') eqn:Eu'.
    { rewrite -> Z.leb_le in Eu'.
      enough (List.nth (abs (a + 1)) L 0 <= List.nth (abs a') L 0) by math.
      apply IIL_L_inc'; math.
    }
    { rewrite -> Z.leb_gt in Eu, Eu'. math. }
  }
Qed.

Lemma IILG0 i : L[i] >= 0.
Proof. 
  enough (0 <= L[i]) by math. 
  case (classicT (abs i < length L))=> C. 2: rewrite (@nth_overflow _ _ (abs i)); try math.
  rewrite <- IIL_L_first at 1. replace (abs i) with (abs (abs i)) by math. apply IIL_L_inc'; math.
Qed.

Lemma IIL_sorted : sorted L.
Proof. unfold sorted. apply IIL_L_inc. Qed.

Section segmentation.

Definition ind_seg (i : int) := 
  interval (List.nth (abs i) L 0) (List.nth (abs (i + 1)) L 0).

Lemma interval_segmentation_pre i :
  (0 <= i < (length L)) -> 
  Union (interval 0 i) ind_seg = interval 0 (List.nth (abs i) L 0).
Proof. 
  remember (to_nat i) as n.
  revert i Heqn.
  induction n as [ | n IH ]; intros.
  { assert (i = 0) as -> by math. 
    rewrite -> IIL_L_first. simpl. rewrite -> intervalgt; try math.
    by rewrite -> Union0.
  }
  { assert (i = n + 1) as -> by math.
    rewrite -> intervalUr; try math.
    rewrite -> Union_upd_fset, -> IH; try math.
    unfold ind_seg. 
    rewrite <- interval_union with (x:=0) (y:=(List.nth (abs n) L 0))
      (z:=(List.nth (abs (n + 1)) L 0)); try math.
    2:{
      rewrite <- IIL_L_first at 1. 
      destruct n; try math. 
      apply IIL_L_inc'; math. 
    }
    2: apply IIL_L_inc'; math. 
    rewrite -> union_comm_of_disjoint. 1: reflexivity.
    apply disjoint_of_not_indom_both.
    intros. rewrite -> indom_interval in *. math.
  }
Qed.

Lemma ind_seg_disjoint (i j : int) (Hi : indom (interval 0 (length L - 1)) i)
  (Hj : indom (interval 0 (length L - 1)) j) (Hn : i <> j) : disjoint (ind_seg i) (ind_seg j).
Proof.
  unfold ind_seg. 
  rewrite -> indom_interval in Hi, Hj.
  destruct Hi as (Hi1 & Hi2), Hj as (Hj1 & Hj2).
  apply disjoint_of_not_indom_both.
  intros x Hi Hj. rewrite -> indom_interval in Hi, Hj.
  destruct (Z.leb (i + 1) j) eqn:E.
  { rewrite -> Z.leb_le in E.
    apply IIL_L_inc' in E; try math.
  }
  { destruct (Z.leb (j + 1) i) eqn:E'.
    { rewrite -> Z.leb_le in E'.
      apply IIL_L_inc' in E'; try math.
    }
    rewrite -> Z.leb_gt in E, E'.
    math.
  }
Qed.

Lemma interval_segmentation :
  Union (interval 0 (length L - 1)) ind_seg = interval 0 N.
Proof.
  rewrite -> interval_segmentation_pre with (i:=(length L - 1)). 2: pose proof IIL_L_notnil; math.
  now subst N.
Qed.

End segmentation.

End search_pure_facts.

Corollary interval_unionE (l : list int) N : 
  sorted l -> l[0] = 0 ->
  max l = N ->
  `[0, N] = \U_(i <- `[0, length l -1]) `[l[i], l[i+1] ].
Proof.
  intros. case (classicT (l = nil))=> [ E | Hneq ].
  1: subst l; rewrite !intervalgt ?Union0 //; simpl in *; try math.
  apply notnil_length in Hneq.
  assert (IncreasingIntList l) by (constructor; auto).
  rewrite -> interval_segmentation with (N:=N); auto.
  replace (abs _) with (length l - 1)%nat by math.
  apply notnil_length in Hneq.
  rewrite (nth_last 0 0) // sorted_last_max //.
Qed.
