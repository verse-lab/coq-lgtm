Set Implicit Arguments.
From SLF Require Import LabType Fun LibSepFmap Sum.
From SLF Require Import LibSepReference LibSepTLCbuffer Struct Unary Loops COO.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.


Definition to_int (v : val) : int := 
  match v with 
  | val_int i => i 
  | _ => 0
  end.

Coercion to_int : val >-> Z.

Lemma to_int_if P a b : 
  to_int (If P then a else b) = If P then a else b.
Proof. by case: classicT. Qed.

Section pure_facts.

Import List.

Definition sorted (l : list int) : Prop. Admitted.


End pure_facts.

Module sparse_vec.

Module Export AD := WithUnary(IntDom).

Notation "H1 '\\*' H2" := (hstar H1 H2)
  (at level 42, right associativity, format "H1  \\* '//' H2") : hprop_scope.

Section sparse_vec.

Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.
Notation "'yind'" := ("y_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'yval'" := ("y_val":var) (in custom trm at level 0) : trm_scope.
Notation "'iX'" := ("iX":var) (in custom trm at level 0) : trm_scope.
Notation "'iY'" := ("iY":var) (in custom trm at level 0) : trm_scope.
Notation "'ans'" := ("ans":var) (in custom trm at level 0) : trm_scope.

Import List.

Context (xind xval yind yval : list int).
Context (Nx Ny M : int).
Hypothesis len_xind : length xind = Nx :> int.
Hypothesis len_xval : length xval = Nx :> int.
Hypothesis len_yind : length yind = Ny :> int.
Hypothesis len_yval : length yval = Ny :> int.
Hypothesis sorted_xind : sorted xind.
Hypothesis sorted_yind : sorted yind.
Hypothesis xind_leq : forall x, In x xind -> 0 <= x < M.
Hypothesis yind_leq : forall x, In x yind -> 0 <= x < M.

Definition get := coo_vec.get.

Notation "'while' C '{' T '}'"  :=
  (While C T)
  (in custom trm at level 69,
    C, T at level 0,
    format "'[' while  C ']'  '{' '/   ' '[' T  '}' ']'") : trm_scope.

Definition dotprod := <{
  fun xind xval yind yval =>
    let ans = 0 in
    let iX = ref 0 in 
    let iY = ref 0 in 
    let "iXl" = iX < Nx in 
    let "iYl" = iY < Ny in
    let "cnd" = "iXl" && "iYl" in 
      while "cnd" {
        let "iXind" = xind[iX] in 
        let "iYind" = yind[iY] in 
        let "cnd" = "iXind" = "iYind" in 
        if "cnd" then 
          let "iXind" = xval[iX] in 
          let "iYind" = yval[iY] in 
          let "val" = "iXind" * "iYind" in
          ans += "val";
          ++iX;
          ++iY
        else 
          let "cnd" = "iXl" < "iYl" in 
          if "cnd" then 
            ++iX 
          else ++iY
      }; ans
}>.

Lemma dotprod_spec `{Inhab D} (x_ind x_val y_ind y_val : loc) : 
  {{ arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \*
     arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩ \\*
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, M]) arr(y_ind, yind)⟨3, i⟩) \\*
     (\*_(i <- `[0, M]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    [1| ld in `{0}   => dotprod x_ind x_val y_ind y_val];
    [2| ld in `[0,M] => get Nx ld x_ind x_val];
    [3| ld in `[0,M] => get Ny ld y_ind y_val]
  }]
  {{ hv, \[hv[`1](0) = Σ_(i <- `[0,M]) (hv[`2](i) * hv[`3](i))] \* \Top}}.
Proof.
Admitted.


End sparse_vec.

End sparse_vec.