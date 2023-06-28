From SLF Require Export LibCore.
From SLF Require Export LibSepFmap.

From mathcomp Require Import ssreflect ssrfun .

Set Implicit Arguments.

Section LabeledType.

From mathcomp Require Import seq ssrbool ssrnat ssreflect ssrfun choice.

Section Gen.

Context (T : Type) (def : T).

Definition labType := (int * int)%type.

Record labeled := Lab {
  lab  :  labType; 
  el   :> T;
}.

Definition lab_eqb (l1 l2 : labType) : bool :=
  Z.eqb l1.1 l2.1 && Z.eqb l1.2 l2.2.

Lemma eqbxx l : lab_eqb l l.
Proof. by case: l=> ??; rewrite /lab_eqb Z.eqb_refl Z.eqb_refl. Qed.

Lemma eqbxx' l : lab_eqb l l = true.
Proof. by case: l=> ??; rewrite /lab_eqb Z.eqb_refl Z.eqb_refl. Qed.

Lemma lab_neqd l l' : is_true (negb (lab_eqb l' l)) -> l <> l'.
Proof. by move=> /[swap]->; rewrite eqbxx'. Qed.

Lemma lab_eqbP l l' : lab_eqb l l' -> l = l'.
Proof. 
  rewrite /lab_eqb istrue_and_eq -?bool_eq_true_eq ?Z.eqb_eq=> -[].
  by case: l  l'=> ?? []??/=->->. 
Qed.

Lemma lab_eqb_sym l l' :  lab_eqb l l' = lab_eqb l' l.
Proof. by rewrite /lab_eqb Z.eqb_sym [l.2 =? _]Z.eqb_sym. Qed.

Infix "==" := lab_eqb (at level 10, no associativity).
Infix "!=" := (fun x y => ~~ lab_eqb x y) (at level 10, no associativity).

Definition labSeq := seq labeled.

Fixpoint lookup (s : labSeq) (l : labType) : labeled := 
  if s is (Lab l' x) :: s then 
    if l == l' then 
      (Lab l' x)
    else lookup s l
  else Lab l def.

Definition remove (s : labSeq) (l : labType) := 
  [seq lt <- s | lab lt != l].

Definition has_lab (s : labSeq) (l : labType) :=
  has (fun x => lab x == l) s.

Lemma hasnt_lab s l : 
  ~ has_lab s l -> 
    s = remove s l.
Proof.
  elim: s=>//h t Hi/=.
  move/negP; rewrite negb_or=>/andP; case=>H1 H2.
  case: ifP=>[_|/negbFE]; first by congr (_ :: _); apply: Hi; apply/negP.
  by move=> H3; move: H3 H1=>/lab_eqbP->/negP; case; apply: eqbxx.
Qed.

End Gen.

Infix "==" := lab_eqb (at level 20, no associativity).
Infix "!=" := (fun x y => ~~ lab_eqb x y) (at level 10, no associativity).

Context (S : Type) (T : Type) (def : T).

Definition label (lfs : labeled (fset T)) : fset (labeled T). 
Proof using. Admitted.

(* Search  *)

Definition lab_funs (f : labSeq (S -> T)) : labeled S -> T :=
  fun ls => el (nth (Lab (0, 0)%Z (fun=>def)) f (find (fun x => lab x == lab ls) f)) (el ls).

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
  (* by rewrite/lab_fun_upd; move/(negPP eqP)/negbTE->.
Qed. *)
Admitted.

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
  move=> c x; move: (c (Lab (0,0)%Z x)).
  rewrite /labf_of /=; by case.
Qed.

Lemma labf_ofK' {T S} (f : T -> S) g : 
  cancel f g ->
  cancel (labf_of f) (labf_of g).
Proof. by move=> c [?? /=]; rewrite /labf_of /=; rewrite c. Qed.
