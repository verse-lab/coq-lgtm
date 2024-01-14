Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibListExt LibSepTLCbuffer.
From LGTM.lib.seplog Require Import NTriple LibSepReference LibWP LibSepSimpl LibArray LibLoops.
From LGTM.experiments Require Import Prelude UnaryCommon.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Section tmp.

Context {Dom : Type}.

Local Notation D := (labeled Dom).
Local Notation hhprop := (hhprop D).

Lemma xfor_align `{INH: Inhab D} {A B : Type} Inv
  s vr
  Z N (i j : int) (C1 C1' C2 C2' : trm)
  (Pre : hhprop) Post: 
  (forall (l : int), 
    Z <= l < N ->
    {{ Inv l }}
      [{
        {i| _ in s  => subst vr l C1};
        {j| _ in s  => subst vr l C2}
      }]
    {{ hv, 
        Inv (l + 1) }}) ->
  (i <> j) ->
  (Z <= N)%Z ->
  (forall (t : val), subst "for" t C1 = C1) -> 
  (forall (t : val), subst "cnt" t C1 = C1) ->
  (forall (t : val), subst "cond" t C1 = C1) ->
  (forall (t : val), subst "for" t C2 = C2) -> 
  (forall (t : val), subst "cnt" t C2 = C2) ->
  (forall (t : val), subst "cond" t C2 = C2) ->
  var_eq vr "cnt" = false ->
  var_eq vr "for" = false ->
  var_eq vr "cond" = false ->
  (Pre ==> Inv Z) ->
  ({{ Inv N }}
    [{
      {i| _ in s  => C1'};
      {j| _ in s  => C2'}
    }]
  {{ hv, Post hv }}) ->
{{ Pre }}
    [{
      {i| _  in s => trm_seq (For Z N (trm_fun vr C1)) C1'};
      {j| _  in s => trm_seq (For Z N (trm_fun vr C2)) C2'}
    }]
  {{ hv, Post hv }}.
Proof.
Admitted.

Lemma xdiv j `{INH: Inhab D} i (Pre : hhprop) Post C1 C2 s:
  i <> j ->
  {{ Pre }}
  [{
    {i| x in s => C1 x};
    {j| x in s => C2 x}
  }]
  {{ hv, Post hv }} ->
  {{ Pre }}
  [{
    {i| x in s => trm_seq (C1 x) (C2 x)}
  }]
  {{ hv, Post hv }}.
Admitted.

End tmp.


Module ll. 

Section ll.

Notation "'curr'" := ("curr":var) (in custom trm at level 0) : trm_scope.
Notation "'h'" := ("h":var) (in custom trm at level 0) : trm_scope.
Notation "'p'" := ("p":var) (in custom trm at level 0) : trm_scope.
Notation "'q'" := ("q":var) (in custom trm at level 0) : trm_scope.
Notation "'i'" := ("i":var) (in custom trm at level 0) : trm_scope.

Context (N : int) (H : 0 <= N).

Definition alloc := 
  <{
    fun h => 
      let curr = ref h in 
      for i <- [0,N] {
        let p = ref 0 in 
        let q = !curr in 
        q := p;
        curr := p
      };
      free curr
  }>.

Definition dealloc := 
  <{
    fun h => 
      let curr = ref h in 
      for i <- [0,N] {
        let p = !curr in 
        let q = !p in 
        free p;
        curr := q
      }; 
      let p = !curr in
      free p;
      free curr
  }>.


Ltac fold' := 
  rewrite ?label_single ?wp_single
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Local Notation D := (labeled unit).

Notation "p '|-(' l ')->' v" := (hsingle (p)%nat (LibLabType.Lab (l,0)%Z tt) v) (at level 32, format  "p  |-( l )->  v").

Lemma allocK `{Inhab D} (x : loc) : 
  {{ x |-(1)-> 0 }}
  [{
    [1| _ in `{tt} => alloc x; dealloc x]
  }]
  {{ _, \[] }}.
Proof with fold'; try lia.
  apply/(@xdiv _ 2)=> //.
  xin 1: xstep=> curr1...
  xin 2: xstep=> curr2...
  eapply xfor_align with 
  (Inv := 
    fun => \exists p : loc, 
      curr1 |-(1)-> p \\* 
      curr2 |-(2)-> p \\*
      p |-(1)-> 0)=> //; eauto... 
  { move=> *; xnsimpl=> {}x.
    xin 1: xstep=> p; xgo.
    replace 
      (x |-(1)-> p) with (x |-(2)-> p) by skip.
    rewrite -xnwp1_lemma /=.
    xgo; xsimpl. }
  { xsimpl. }
  xnsimpl=> {}x.
  replace 
    (x |-(1)-> 0) with (x |-(2)-> 0) by skip.
  xin 1: xstep; rewrite -xnwp1_lemma /=.
  by xgo.
Admitted.

  
End ll.


End ll.

