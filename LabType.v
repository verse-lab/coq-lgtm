From SLF Require Export LibCore.
From SLF Require Export LibSepFmap.

From mathcomp Require Import ssreflect ssrfun.

Set Implicit Arguments.

Section LabeledType.

From mathcomp Require Import seq ssrbool ssrnat eqtype ssreflect ssrfun.

Section Gen.

Context (T : Type) (def : T).

Definition labType := nat.

Record labeled := Lab {
  lab  :  labType; 
  el   :> T;
}.

Definition labSeq := seq labeled.

Definition lookup (s : labSeq) (l : labType) : labeled := 
  nth (Lab 0%nat def) s (find [pred lt | lab lt == l] s).

Definition remove (s : labSeq) (l : labType) := 
  [seq lt <- s | lab lt != l].

Definition has_lab (s : labSeq) (l : labType) :=
  has (fun x => lab x == l) s.

Lemma hasnt_lab s l : 
  ~ has_lab s l -> 
    s = remove s l.
Proof using.
Admitted.

End Gen.

Context (S : Type) (T : Type) (def : T).

Definition lab_union (fss : labSeq (fset T)) : fset (labeled T).
Proof using. Admitted.
Definition label (lfs : labeled (fset T)) : fset (labeled T). 
Proof using. Admitted.
Definition lab_funs (f : labSeq (S -> T)) : labeled S -> T :=
  fun ls => 
    el (nth (Lab 0%nat (fun=> def)) f (lab ls)) (el ls).

Definition lab_fun (f : labeled (S -> T)) : labeled S -> T :=
  fun ls => el f (el ls).

Definition labf_of (f : S -> T) : labeled S -> labeled T :=
  fun ls => Lab (lab ls) (f (el ls)).

Definition lab_fun_upd (f g : labeled S -> T) l : labeled S -> T :=
  fun ls => 
    if lab ls == l then f ls else g ls.

Lemma lab_fun_upd_neq f g l (l' : labType) x : 
  l' <> l -> lab_fun_upd f g l (Lab l' x) = g (Lab l' x).
Proof.
  by rewrite/lab_fun_upd; move/(negPP eqP)/negbTE->.
Qed.

Definition app_lab (f : labeled S -> T) : labType -> S -> T := 
  fun l s => f (Lab l s).

End LabeledType.

Lemma label_single {T} (t : T) l : 
  label (Lab l (single t tt)) = single (Lab l t) tt.
Proof using.
Admitted.

Lemma label_empty {T} l : 
  label (Lab l empty) = empty :> fset (labeled T).
Proof using.
Admitted.

Lemma label_update {T : Type} (fs : fset T) t l : 
  label (Lab l (update fs t tt)) = update (label (Lab l fs)) (Lab l t) tt.
Proof using.
Admitted.

Lemma indom_label_eq {T} l (fs : fset T) l' x :
  indom (label (Lab l fs)) (Lab l' x) = (l = l' /\ indom fs x).
Proof.
Admitted.

Lemma labf_ofK {T S} (f : T -> S) g : 
  cancel (labf_of f) (labf_of g) -> 
  cancel f g.
Proof.
  move=> c x; move: (c (Lab 0%nat x)).
  rewrite /labf_of /=; by case.
Qed.

Lemma labf_ofK' {T S} (f : T -> S) g : 
  cancel f g ->
  cancel (labf_of f) (labf_of g).
Proof. by move=> c [?? /=]; rewrite /labf_of /=; rewrite c. Qed.