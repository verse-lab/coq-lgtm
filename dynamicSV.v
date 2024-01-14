Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl LibArray LibLoops.
From LGTM.lib.theory Require Import LibListExt.
From LGTM.experiments Require Import Prelude UnaryCommon.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.
Import List Vars.

Local Notation D := (labeled int).
Local Notation hhprop := (hhprop D).

Definition field : Type := nat.
Definition hrecord_field : Type := (field * val).
Definition hrecord_fields : Type := list hrecord_field.

Definition hfield (p:loc) (k:field) (v:val) (d : D) : hhprop :=
  ((p+1+k)%nat ~(d)~> v).

Fixpoint hfields (kvs:hrecord_fields) (p:loc) (d : D) : hhprop :=
  match kvs with
  | nil => \[]
  | (k,v)::kvs' => (hfield p k v d) \* (hfields kvs' p d)
  end.

Definition maps_all_fields (n:nat) (kvs:hrecord_fields) : Prop :=
  LibList.map fst kvs = nat_seq 0 n.

Definition hrecord (kvs:hrecord_fields) (p:loc) (d : D) : hhprop :=
  (hexists (fun (n: nat) => hheader n p d \* hfields kvs p d \* \[maps_all_fields n kvs])).

Definition index : field := 0%nat.
Definition value : field := 1%nat.
Definition next : field := 2%nat.

Fixpoint MList (L:list (val * val)) (p:loc) (d : D) : hhprop :=
  match L with
  | nil => \[(p, d) = null d]
  | (i,v)::L' => \exists q, (hrecord ((index,i)::(value,v)::(next,val_loc q)::nil) p d) \* (MList L' q d)
  end.

Definition val_get_field (k:field) : val :=
  <{ fun 'p =>
       let 'p1 = val_ptr_add 'p 1 in
       let 'q = val_ptr_add 'p1 {k} in
       val_get 'q }>.

Notation "t1 '`.' f" :=
  (val_get_field f t1)
    (in custom trm at level 56, f at level 0, format "t1 '`.' f" ).


Definition null : loc := 0%nat.

Notation "'ind'" := ("ind":var) (in custom trm at level 0) : trm_scope.
Notation "'length'" := ("length":var) (in custom trm at level 0) : trm_scope.
Notation "'output'" := ("output":var) (in custom trm at level 0) : trm_scope.
Notation "'p'" := ("p":var) (in custom trm at level 0) : trm_scope.
Notation "'a'" := ("a":var) (in custom trm at level 0) : trm_scope.
Notation "'i'" := ("i":var) (in custom trm at level 0) : trm_scope.

Context (row : list (val * val)).
Context (dvec : list int).
Context (M : int).

Definition linkedList_get :=
  <{
      fun p ind =>
        let "c" = ("p" = null) in 
        while (val_neg "c") {
            let i = 'p`.index in 
            if "i = ind" then 
              'p`.value
            else
              'p := 'p`.next
          };
      0
    }>.

Definition map_b :=
  <{
      fun p a =>
        let output = ref 0 in 
        let "c" = ("p" = null) in 
        while (val_neg "c") {
            let "ind" = 'p`.index in 
            let "v" = 'p`.value in
            "output" += ("v" * (val_array_get a "ind"));
            'p := 'p`.next
          };
      !"output"
    }>.


Fixpoint getIndexes (l : list (val * val)) :=
  match l with
  | nil => nil 
  | (index, value) :: tl =>
      match index with
      | val_int v => v :: getIndexes tl
      | _ => nil (* should not match *) 
      end
  end.

Lemma ll_get_spec_out `{Inhab D} fs (ll : loc) : 
  @htriple D fs
    (fun i => linkedList_get ll (eld i)) 
    (\[forall d, indom fs d -> ~ In (eld d) (getIndexes row)])
    (fun hr => 
       \[hr = fun=> 0]).
Proof.
  xwp; xsimpl=> ?. xapp=> v0. xwp; eauto. 
  Admitted.

(* 
Lemma ll_get_spec_out_unary {D : Type} `{Inhab D} (ll : loc) (i : int) (d : D) : 
  @htriple D (single d tt)
    (fun=> linkedList_get ll i)            
    (\[~ In i (getIndexes row)] \*
      MList row ll d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      MList row ll d).
Proof. Admitted.
*)

Tactic Notation "seclocal_solver" :=
  first [ rewrite list_interval_nth'; auto; try math
        | rewrite list_interval_length; auto; math
        | rewrite -list_interval_nth; auto; math
        | idtac ]; auto.

Ltac fold' := 
  rewrite ?label_single ?wp_single ?val_int_eq
    -/(While_aux _ _) 
    -/(While _ _) //=; try lia.

Lemma dv_dotprod `{Inhab (labeled int)} (ll d_vec : loc) : 
  {{   (MList row ll (Lab (1, 0) 0)) \*
        (MList row ll (Lab (2, 0) 0)) \*
        (\*_(i <- `[0, M]) arr(d_vec, dvec)⟨3, i⟩)                                    
  }}
    [{
        {1| ld in `{0} => map_b ll d_vec };
        {2| ld in `[0,M] => linkedList_get ll ld}
    }]
    {{ hv, (\[hv[`1](0) = Σ_(i <- `[0,M]) (hv[`2](i) * dvec[i])] \* 
             (MList row ll (Lab (1,0) 0)) \*
            (MList row ll (Lab (2, 0) 0))) \*
            (\*_(i <- `[0, M]) arr(d_vec, dvec)⟨2, i⟩) }}.
Proof with (try solve [ seclocal_solver ]; fold').
  xset_Inv Inv 1; xset_R int Inv R 2.
  set (ind := getIndexes row).
  xfocus* 2 ind. xapp ll_get_spec_out=> //. 1: case=> ??; indomE; autos*.
  xin 1 : xwp; xapp=> ans; xwp; xapp=> i...
  set (R1 (i : int) := (MList row ll (Lab (2, 0) 0))).
  set (R2 (i : int) := (arr(d_vec, dvec)⟨2, i⟩)).
  set (cond p := isTrue (p <> (0%nat))).
  set (Inv (b : bool) (i : int) :=
         (MList row ll (Lab (1, 0) 0)) \*
           \exists (p : loc), \[ b = cond p ]).
  set (op hv i := hv[`2](i) * (dvec[i])).
  xwhile_sum Inv R1 R2 R1 R2 op ans.

  
