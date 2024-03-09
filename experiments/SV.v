Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl LibArray LibLoops NTriple.
From LGTM.lib.theory Require Import LibListExt.
From LGTM.experiments Require Import Prelude UnaryCommon.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Module sv.

Section sv.

Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
Notation "'xlb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'xrb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.

Import List Vars list_interval_notation.

Context (xind xval : list int).
Context (N M : int).
Context (lb rb : int).
Hypothesis (len : rb - lb = N).
Hypotheses (bounds_l: 0 <= lb) (bounds_r: lb <= rb).
Hypothesis len_xind : rb <= length xind.
Hypothesis len_xval : rb <= length xval.
Hypothesis nodup_xind : NoDup (xind [[ lb -- rb ]]).
Hypothesis xind_leq : forall x, In x (xind [[ lb -- rb ]]) -> 0 <= x < M.


(* Local automation tactic *)
Tactic Notation "seclocal_solver" :=
  first [ rewrite list_interval_nth'; auto; try math
    | rewrite list_interval_length; auto; math
    | rewrite -list_interval_nth; auto; math
    | idtac ]; auto.

Definition indexf := index_bounded.func.

(* Accessor function for 'extended' SV format. It takes pointers to values 
  and indices arrays `xind` and `xval` as well as the range of where to search 
  for a value -- `xlb` and `xrb`. In case if `xlb = 0` and `xrb = size xind`, 
  `get` will perform the search throug the entier two arrays.  *)
Definition get := 
  <{
  fun i xind xval xlb xrb =>
    let k = indexf xlb xrb i xind in 
    let "k < rb" = k < xrb in
    if "k < rb" then
      xval[k]
    else 0
}>.


(* Unary dummy specification for a getter functions. This specification 
  Just says that `get` doesn't change the head state. It is needed in the 
  `spvspv` verification to hangle `sv_get` vaules multipled by 0 *)
Lemma get_spec {D} `{Inhab D} (x_ind x_val : loc) (d : D) (l : int): 
  htriple (`{d}) (* Domain of a unary triple -- a singleton set `{d}` *)
    (fun=> get l x_ind x_val lb rb) (* we run `get` funtion on this unary domain *)
    (arr(x_ind, xind)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩) (* precondition *)
    (fun hr => 
      arr(x_ind, xind)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩). (* postcondition *)
Proof.
  xwp; xsimpl; xapp @index_bounded.spec=> //. (* apply `index` function spec  *)
  xstep. (* compute the `if` condition *)
  xwp; xif=> ?; (* case analysis on the `if` condition *)
  [xapp|xwp;xval]; xsimpl. (* finish the proof *)
Qed.

(* Unary specification for `sv_get` called on the `i`th element of the 
  `xind[lb..rb]` array *)
Lemma get_spec_in {D : Type} `{Inhab D} (x_ind x_val : loc) i (d : D) : 
  let xindr := xind [[ lb -- rb ]] in (* `lb` to `rb` rangle of `xind` *)
  let xvalr := xval [[ lb -- rb ]] in (* `lb` to `rb` rangle of `xval` *)
  htriple (`{d})
    (fun=> get xindr[i] x_ind x_val lb rb) (* running `sv_get` on `xind[lb..rb][i]` *)
    (\[0 <= i < N] \*
      arr(x_ind, xind)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩)
    (fun hr => 
     \[hr = fun=> xvalr[i] ] \*  (* the output is the singleton hyper-value indexed by {d}, which is equal to `xval[lb..rb][i]` *)
      arr(x_ind, xind)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩).
Proof with seclocal_solver.
  xwp; xsimpl=> ?; xapp (@index_bounded.spec _ H)=> //.
  xstep. rewrite index_nodup; auto...
  xwp; xif=> ?; subst; try math.
  xapp; xsimpl*... 
Qed.

(* Unary specification for `sv_get` called on the index outside of the `xind[lb..rb]` array *)
Lemma get_spec_out_unary {D : Type} `{Inhab D} (x_ind x_val : loc) (i : int) (d : D) : 
  htriple (`{d}) 
    (fun=> get i x_ind x_val lb rb)
    (\[~ In i (xind [[ lb -- rb ]])] \*
      arr(x_ind, xind)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩)
    (fun hr => 
     \[hr = fun=> 0] \* (* the output value is 0 *)
      arr(x_ind, xind)⟨`d⟩ \* 
      arr(x_val, xval)⟨`d⟩).
Proof.
  xwp; xsimpl=> ?; xapp (@index_bounded.spec _ H)=> //...
  rewrite memNindex // list_interval_length //.
  xstep. xwp; xif=> ?; try math. xwp; xval. xsimpl*.
Qed.

Local Notation D := (labeled int).

(* Hyper specification for `sv_get` function, called on a set on indecies,
  outside of the `xind[lb..rb]` array. The index set in this case is a finite 
  set (`fset`) of elements of type `labeled int`. *)
Lemma get_spec_out `{Inhab D} (x_ind x_val : loc) (fs : fset D) (* finite index set *) : 
  htriple fs
    (fun i => get (eld i) x_ind x_val lb rb)
    (\[forall d, indom fs d -> ~ In (eld d) (xind [[ lb -- rb ]])] \*
      (\*_(d <- fs) arr(x_ind, xind)⟨`d⟩ ) \* 
       \*_(d <- fs) arr(x_val, xval)⟨`d⟩)
    (fun hr => 
     \[hr = fun=> 0] \* 
      ((\*_(d <- fs) arr(x_ind, xind)⟨`d⟩) \* 
       \*_(d <- fs) arr(x_val, xval)⟨`d⟩)).
Proof. by xpointwise_build (@get_spec_out_unary). Qed.

(* funtion that sums up elements in the sparse array in SV format *)
Definition sum := 
  <{
  fun xind xval xlb xrb =>
  let s = ref 0 in
  for i <- [xlb, xrb] {
    let x = read_array xval i in 
    s += x
  };
  let "res" = ! s in
  free s;
  "res"
}>.

Ltac fold' := 
  rewrite ?label_single ?wp_single ?val_int_eq
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

(* Specification for the summation function *)
Lemma sum_spec `{Inhab D} (x_ind x_val : loc) (s : int) : 
  {{ arr(x_ind, xind)⟨1, 0⟩ \*
     arr(x_val, xval)⟨1, 0⟩ \\* 
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) }}
  [{
    [1| ld in `{0}         => sum x_ind x_val lb rb];
    {2| ld in `[0, M]      => get ld x_ind x_val lb rb}
  }]
  {{ hv, (\[hv[`1](0) = Σ_(i <- `[0, M]) hv[`2](i)] \* 
      arr(x_ind, xind)⟨1, 0⟩ \*
      arr(x_val, xval)⟨1, 0⟩) \* 
      (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
      (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩)}}.
Proof with (try solve [ seclocal_solver ]; fold').
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus* 2 xind[[lb -- rb]]. (* focusing on non-zero indices of the sparse array *)
  xapp get_spec_out=> //. 1: case=> ??; indomE; autos*. (* prove that remaining indices are zeros, making use of `get_spec_out` *)
  xclean_heap. (* clean up the heap *)
  xin 1 : xstep=> q... (* executing the first instruction in `sum` *)
  have Hl : length xind[[lb -- rb]] = rb - lb :> int by apply list_interval_length.
  rewrite intr_list ?(fset_of_list_nodup 0) ?Hl ?Union_interval_change2 //. (* prepare for `For` rule application *)
  xfor_sum Inv R R (fun hv i => hv[`2](xind[i])) q... (* `For` rule application *)
  { (xin 1: (xstep; xapp (@incr.spec  _ H)=> y))... (* executing the rest of the `sum` *)
    xapp (@get_spec_in D)=> //; try math. xsimpl*... } (* executing getters *)
  { move=>Ha Hb Hc; have Ha' : i0 - lb <> j0 - lb by math.
    move: Ha'; apply contrapose, NoDup_nthZ; autos*; math. } (* minor proof obligation *)
  xstep... xstep. xwp; xval. xsimpl*. (* deallocating the accumulator in `sum` *)
  xsum_normalize. by rewrite intr_list // Sum_list_interval. (* adjusting summations *)
Qed.

Context (dvec : list int).
Context (dvec_len : length dvec = M :> int).

(* Dot product of a sparse SV array and a dense one *)
Definition dotprod := 
  <{
  fun xind xval dvec xlb xrb =>
  let s = ref 0 in
  for i <- [xlb, xrb] {
    let x = xval[i] in 
    let i = xind[i] in 
    let v = dvec[i] in 
    let x = x * v in
    s += x
  };
  let "res" = ! s in
  free s;
  "res"
}>.


(* Specification for the `dotprod` *)
Lemma dotprod_spec `{Inhab D} (x_ind x_val d_vec : loc) : 
  {{ arr(x_ind, xind)⟨1, 0⟩ \\*
     arr(x_val, xval)⟨1, 0⟩ \\*
     arr(d_vec, dvec)⟨1, 0⟩ \\* 
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, M]) arr(d_vec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{0}   => dotprod x_ind x_val d_vec lb rb];
    [2| ld in `[0,M] => get ld x_ind x_val lb rb]
  }]
  {{ hv, \[hv[`1](0) = Σ_(i <- `[0,M]) (hv[`2](i) * dvec[i])] \* 
     arr(x_ind, xind)⟨1, 0⟩ \\*
     arr(x_val, xval)⟨1, 0⟩ \\*
     arr(d_vec, dvec)⟨1, 0⟩ \\* 
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, M]) arr(d_vec, dvec)⟨2, i⟩)}}.
Proof with (try solve [ seclocal_solver ]; fold').
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus* 2 xind[[lb -- rb]].
  xapp get_spec_out=> //. 1: case=> ??; indomE; autos*.
  xclean_heap.
  xin 1 : xwp; xapp=> q...
  have Hl : length xind[[lb -- rb]] = rb - lb :> int by apply list_interval_length.
  rewrite intr_list ?(fset_of_list_nodup 0) ?Hl ?Union_interval_change2 //.
  xfor_sum Inv R R (fun hv i => (hv[`2](xind[i]) * dvec[xind[i] ])) q...
  { (xin 1: do 4 (xwp; xapp); xapp (@incr.spec _ H)=> y)...
    xapp (@get_spec_in D)=> //; try math. xsimpl*... }
  { move=>Ha Hb Hc; have Ha' : i0 - lb <> j0 - lb by math.
    move: Ha'; apply contrapose, NoDup_nthZ; autos*; math. }
  xwp; xapp... xwp; xapp. xwp; xval. xsimpl*.
  xsum_normalize (fun=> Z.mul^~ _). by rewrite intr_list // Sum_list_interval.
Qed.

End sv. 

Section sv.

Import List list_interval_notation.

Context (xind xval yind yval : list int).
Context (Nx Ny M rbx lbx rby lby : int).
(* Hypothesis lenx : rbx - lbx = Nx. *)
(* Hypothesis leny : rby - lby = Nx. *)
Hypothesis (bounds_lx : 0 <= lbx) (bound_rx : lbx <= rbx).
Hypothesis (bounds_ly : 0 <= lby) (bound_ry : lby <= rby).
Hypothesis len_xind : rbx <= length xind.
Hypothesis len_xval : rbx <= length xval.
Hypothesis len_yind : rby <= length yind.
Hypothesis len_yval : rby <= length yval.
Hypothesis sorted_xind : sorted (xind [[ lbx -- rbx ]]).
Hypothesis sorted_yind : sorted (yind [[ lby -- rby ]]).
Hypothesis xind_leq : forall x, In x (xind [[ lbx -- rbx ]]) -> 0 <= x < M.
Hypothesis yind_leq : forall x, In x (yind [[ lby -- rby ]]) -> 0 <= x < M.


(* Notation "'xind'" := ("x_ind":var) (in custom trm at level 0) : trm_scope. *)
(* Notation "'xval'" := ("x_val":var) (in custom trm at level 0) : trm_scope. *)
(* Notation "'yind'" := ("y_ind":var) (in custom trm at level 0) : trm_scope. *)
(* Notation "'yval'" := ("y_val":var) (in custom trm at level 0) : trm_scope. *)
Notation "'rbx'" := ("rb_x":var) (in custom trm at level 0) : trm_scope.
Notation "'lbx'" := ("lb_x":var) (in custom trm at level 0) : trm_scope.
Notation "'rby'" := ("rb_y":var) (in custom trm at level 0) : trm_scope.
Notation "'lby'" := ("lb_y":var) (in custom trm at level 0) : trm_scope.
Notation "'iX'" := ("iX":var) (in custom trm at level 0) : trm_scope.
Notation "'iY'" := ("iY":var) (in custom trm at level 0) : trm_scope.
Notation "'ans'" := ("ans":var) (in custom trm at level 0) : trm_scope.


(* Dot product of two sparse SV arrays. Correspond to `spvspv` from Fig. 3 of the paper *)
Definition sv_dotprod (xind yind xval yval : loc) := <{
  fun lbx rbx lby rby  =>
    let ans = ref 0 in
    let iX = ref lbx in 
    let iY = ref lby in 
      while (
        let "ix" = !iX in
        let "iy" = !iY in
        let "iXl" = "ix" < rbx in 
        let "iYl" = "iy" < rby in
        "iXl" && "iYl") {
        let "ix" = !iX in
        let "iy" = !iY in
        let "iXind" = xind["ix"] in 
        let "iYind" = yind["iy"] in 
        let "cnd" = "iXind" = "iYind" in 
        if "cnd" then 
          let "iXind" = xval["ix"] in 
          let "iYind" = yval["iy"] in 
          let "val" = "iXind" * "iYind" in
          ans += "val";
          ++iX;
          ++iY
        else 
          let "cnd" = "iXind" < "iYind" in 
          if "cnd" then 
            ++iX 
          else ++iY
      }; 
      let "s" = !ans in 
      free iX; free iY; free ans;
      "s"
}>.

Definition arr1 x_ind y_ind x_val y_val := 
  arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \*
  arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩.

Ltac fold' := 
  rewrite ?label_single ?wp_single ?val_int_eq
    -/(While_aux _ _) 
    -/(While _ _) //=; try lia.

Notation size := Datatypes.length.

(* specification of `sv_dotprod` *)
Lemma sv_dotprod_spec `{Inhab (labeled int)} (x_ind x_val y_ind y_val : loc) : 
  {{ (arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \*
     arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩) \*
     (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
     (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) \\* 
     (\*_(i <- `[0, M]) arr(y_ind, yind)⟨3, i⟩) \\*
     (\*_(i <- `[0, M]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    {1| ld in `{0}   => sv_dotprod x_ind y_ind x_val y_val lbx rbx lby rby};
    {2| ld in `[0,M] => get ld x_ind x_val lbx rbx};
    {3| ld in `[0,M] => get ld y_ind y_val lby rby}
  }]
  {{ hv, \[hv[`1](0) = Σ_(i <- `[0,M]) (hv[`2](i) * hv[`3](i))] \* 
      (arr(x_ind, xind)⟨1, 0⟩ \* arr(y_ind, yind)⟨1, 0⟩ \*
      arr(x_val, xval)⟨1, 0⟩ \* arr(y_val, yval)⟨1, 0⟩) \*
      (\*_(i <- `[0, M]) arr(x_ind, xind)⟨2, i⟩) \\*
      (\*_(i <- `[0, M]) arr(x_val, xval)⟨2, i⟩) \\* 
      (\*_(i <- `[0, M]) arr(y_ind, yind)⟨3, i⟩) \\*
      (\*_(i <- `[0, M]) arr(y_val, yval)⟨3, i⟩)}}.
Proof with fold'.
  set (sxind := (xind [[ lbx -- rbx ]])).
  set (syind := (yind [[ lby -- rby ]])).
  set (sxval := (xval [[ lbx -- rbx ]])).
  set (syval := (yval [[ lby -- rby ]])).
  pose proof (size_merge sxind syind) as indlen.
  set (ind := merge sxind syind) in indlen |- *.
  have indsorted : sorted ind by rewrite /sxind/syind; apply sorted_merge.
  have?: NoDup sxind by exact/sorted_nodup.
  have?: NoDup syind by exact/sorted_nodup.
  have ndind: NoDup ind by exact/sorted_nodup.
  rewrite -/(arr1 _ _ _ _).
  xfocus* 2 ind.
  xapp (@get_spec_out xind xval); eauto. 
  1: case=> ??; indomE; rewrite /LibSummation.mem/ind In_merge; autos*.
  xclean_heap.
  xfocus* 3 ind.
  xapp (@get_spec_out yind yval); eauto.
  1: case=> ??; indomE; rewrite /LibSummation.mem/ind In_merge; autos*.
  xclean_heap.
  set (H1 := _ \* hbig_fset _ _ _); set (H2 := _ \* H1); set (arrs := _ \* H2).
  xin 1 : xwp; xapp=> ans; xwp; xapp=> iX; xwp; xapp=> iY...
  have Hlx : length sxind = rbx - lbx :> int by apply list_interval_length.
  have Hly : length syind = rby - lby :> int by apply list_interval_length.
  have E : `[0,M] ∩ ind = ind.
  { apply intr_list=> x. rewrite In_merge /sxind/syind. case; [ apply xind_leq | apply yind_leq ]; auto. }
  rewrite ?E (fset_of_list_nodup 0) //.
  set (cond ix iy := isTrue (ix < rbx /\ iy < rby)).
  set (Inv (b : bool) (i : int) := 
    arr1 x_ind y_ind x_val y_val \*
    \exists (ix iy : int), 
      iY ~⟨(1, 0)%Z, 0⟩~> iy \* iX ~⟨(1, 0)%Z, 0⟩~> ix \*
      \[(i = size ind -> ~ b) /\ lbx <= ix /\ lby <= iy /\
        (i < size ind -> ind[i] > max (take (abs (ix - lbx)) sxind)) /\
        (i < size ind -> ind[i] > max (take (abs (iy - lby)) syind)) /\ 
        b = cond ix iy /\
        (b -> 
          (ind[i] = Z.min xind[ix] yind[iy] /\ 
          (forall x, In x sxind -> x < xind[ix] -> x < yind[iy]) /\  
          (forall y, In y syind -> y < yind[iy] -> y < xind[ix])))]).
  set (op hv i := hv[`2](ind[i]) * hv[`3](ind[i])).
  set (R1 (i : int) := arr(y_ind, yind)⟨3,i⟩ \* arr(y_val, yval)⟨3,i⟩).
  set (R2 (i : int) := arr(x_ind, xind)⟨2,i⟩ \* arr(x_val, xval)⟨2,i⟩).
  enough (xindE : forall i, lbx <= i < rbx -> xind[i] = sxind[i-lbx]).
  enough (yindE : forall i, lby <= i < rby -> yind[i] = syind[i-lby]).
  enough (xvalE : forall i, lbx <= i < rbx -> xval[i] = sxval[i-lbx]).
  enough (yvalE : forall i, lby <= i < rby -> yval[i] = syval[i-lby]).
  2-5: move=> *; rewrite list_interval_nth'...
  have xind_ge_0 : forall i, lbx <= i < rbx -> 0 <= xind[i].
  { move=> *. rewrite xindE //. apply xind_leq, nth_In_int. rewrite Hlx. math. } 
  have yind_ge_0 : forall i, lby <= i < rby -> 0 <= yind[i].
  { move=> *. rewrite yindE //. apply yind_leq, nth_In_int. rewrite Hly. math. }
  have sE : forall a b, a - b + 1 = a + 1 - b by lia.
  xwhile_sum Inv R1 R2 R1 R2 op ans=> //.
  { move=> l s ?.
    rewrite {1}/Inv; xnsimpl=> ix iy[?][?][?][LM1][LM2][].
    rewrite /cond. bool_rew=> -[??]/(_ eq_refl)-[]indlE[L1 L2].
    rewrite /arr1; clear arrs H1 H2.
    have max_ind_ge_max_sxind : max ind >= max sxind by apply/max_sublist; try math; move=>?; rewrite In_merge; left.
    have max_ind_ge_max_syind : max ind >= max syind by apply/max_sublist; try math; move=>?; rewrite In_merge; right.
    have max_sxind_lt_M : max sxind <= M by apply/Z.lt_le_incl/max_upperbound_lt; try math; move=>??; apply xind_leq.
    have max_syind_lt_M : max syind <= M by apply/Z.lt_le_incl/max_upperbound_lt; try math; move=>??; apply yind_leq.
    xin 1: do 5 (xwp; xapp); xwp; xif=> C.
    { xin 1: 
        do 3 (xwp; xapp); xwp; xapp @incr.spec; 
        (xwp; xapp @incr1.spec); xapp @incr1.spec=> ?.
      rewrite /op /=; rewrite <-?hstar_assoc.
      set (Heap := _ \* harray_int xind _ _); rewrite /R2...
      rewrite val_int_eq in C; rewrite {-1 4 6}indlE -C Z.min_id xindE...
      xin 2: fold'; xapp get_spec_in; eauto...
      rewrite /R1 indlE C Z.min_id yindE...
      xapp get_spec_in; eauto...
      rewrite /Heap /Inv /arr1/cond.
      have SlE: 
        l + 1 = size ind -> 
          ~ (ix - lbx + 1 < rbx - lbx /\ iy - lby + 1 < rby - lby). 
      { move: C indlE=>-> /[! Z.min_id]/[swap]/sorted_max_size->; bool_rew; try math; try assumption.
        rewrite yindE...
        move: max_ind_ge_max_syind=>/[swap]->/nth_le_max-> //; lia. }
      rewrite -xvalE -?yvalE...
      xsimpl (ix + 1) (iy + 1); splits; [|lia|lia| | |autos*|]...
      { bool_rew... }
      { move=> ?; rewrite -sE max_takeS -?xindE; auto... 
        suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia. }
      { replace (iy + 1 - lby) with (iy - lby + 1) by lia.
        move=> ?; rewrite max_takeS -?yindE; auto...
        suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia. }
      bool_rew=> -[]??; splits*.
      { rewrite (merge_nthS (def:=M)) // -/ind; try lia; try (solve [ rewrite notnil_length; math ]).
        rewrite indlE {2}C -{1}C ?Z.min_id xindE ?yindE ?search_nth...
        rewrite xindE ?yindE; first do 2 f_equal... }
      { move=> x ??; move: (@sorted_le (iy -lby) (iy +1 - lby) syind sorted_yind).
        rewrite -?yindE...
        suff: (x <= xind[ix]) by lia.
        rewrite xindE; first apply/In_lt; rewrite ?sE -?xindE... }
      move=> y ??; move: (@sorted_le (ix -lbx) (ix +1 - lbx) sxind sorted_xind).
      rewrite -?xindE...
      suff: (y <= yind[iy]) by lia.
      rewrite yindE; first apply/In_lt; rewrite ?sE -?yindE... }
    rewrite /op.
    xin 1: xwp; xapp; xwp; xif=> L; xapp @incr1.spec=> ?.
    { rewrite /op /=; rewrite <-?hstar_assoc.
      set (Heap := _ \* harray_int yval _ _); rewrite /R2...
      rewrite indlE Z.min_l... rewrite (xindE ix)...
      xin 2: fold'; xapp get_spec_in; eauto...
      rewrite /R1; xapp get_spec_out_unary; eauto.
      { move/L2; rewrite -xindE... }
      rewrite Z.mul_0_r Z.add_0_r.
      rewrite /Heap /Inv /arr1/cond.
      have SlE: 
        l + 1 = size ind -> 
          ~ (ix - lbx + 1 < rbx - lbx /\ iy - lby < rby - lby). 
      { move: indlE=> /[!Z.min_l] //; last lia. 
        move=>/[swap]/sorted_max_size->; bool_rew; try math; try assumption.
        move: max_ind_ge_max_sxind=>/[swap]->; rewrite xindE... move/nth_le_max->... }
      xsimpl (ix + 1) (iy); splits; [|lia|lia| | |autos*|].
      { bool_rew... }
      { move=> ?; rewrite -sE max_takeS -?xindE; auto...
        suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia. }
      { move=> ?. suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia. }
      bool_rew=> -[]??; splits*.
      { rewrite (merge_nthS (def:=M)) -/ind ?indlE 1?(Z.min_l (_[_])); try (solve [ rewrite notnil_length; math ])...
        rewrite xindE ?search_nth ?sE -?xindE ?yindE...
        erewrite search_lt_nth; eauto...
        all: rewrite -yindE...
        move=> ? /L2; lia. }
      { move=> x ??; move: (@sorted_le (ix -lbx) (ix +1 - lbx) sxind sorted_xind).
        rewrite -?xindE...
        suff: (x <= xind[ix]) by lia.
        rewrite xindE; first apply/In_lt; rewrite ?sE -?xindE... }
      move=> ? /L2/[apply]; rewrite ?xindE...
      move:  (@sorted_le (ix -lbx) (ix +1 - lbx) sxind sorted_xind)... }
    rewrite /op /=; rewrite <-?hstar_assoc.
    set (Heap := _ \* harray_int yval _ _); rewrite /R1...
    rewrite indlE Z.min_r... rewrite (yindE iy)...
    xin 3: fold'; xapp get_spec_in...
    rewrite /R2; xapp get_spec_out_unary; eauto.
    { move/L1. rewrite val_int_eq in C; rewrite -yindE... }
    rewrite Z.mul_0_l Z.add_0_r.
    have SlE: 
    l + 1 = size ind -> 
      ~ (ix - lbx < rbx - lbx /\ iy - lby + 1 < rby - lby). 
    { move: indlE=> /[!Z.min_r] //; last lia. 
      move=>/[swap]/sorted_max_size->; bool_rew; try math; try assumption.
      move: max_ind_ge_max_syind=>/[swap]->; rewrite yindE... move/nth_le_max->... }
    rewrite val_int_eq in C.
    rewrite /Heap /Inv /arr1/cond; xsimpl (ix) (iy+1); splits; [|lia|lia| | |autos*|].
    { bool_rew... }
    { move=> ?. suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia. }
    { move=> ?; rewrite -sE max_takeS -?yindE; auto...
      suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia. }
    bool_rew=> -[]??; splits*.
    { rewrite (merge_nthS (def:=M)) -/ind ?indlE 1?(Z.min_r (_[_])); try (solve [ rewrite notnil_length; math ])...
      rewrite yindE ?search_nth ?sE -?yindE ?xindE...
      erewrite search_lt_nth; eauto...
      all: rewrite -xindE...
      move=> ? /L1; lia. }
    { move=> ? /L1/[apply]; rewrite ?yindE...
      move: (@sorted_le (iy - lby) (iy+1-lby) syind sorted_yind); lia. }
    move=> y ??; move: (@sorted_le (iy -lby) (iy +1 - lby) syind sorted_yind).
    rewrite -yindE...
    suff: (y <= yind[iy]) by lia.
    rewrite yindE; first apply/In_lt; rewrite ?sE -?yindE... }
  { move=> l *; rewrite /Inv/op/ntriple.
    xpull=> ix iy []_[]?[]?[]L1[]L2; rewrite /cond; bool_rew=> /[!not_and_eq]-[] []G _.
    { rewrite /R1.
      xin 3: fold'; xapp get_spec=> *...
      rewrite /R2.
      xapp get_spec_out_unary...
      { move/max_le; move: L1; rewrite take_ge ?length_List_length; try math.
        rewrite -/sxind; lia. }
      xsimpl; try math.
      splits*=> //.
      { move=> ?. suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia. }
      { move=> ?. suff: ind[l] < ind[l+1] by lia.
        apply/sorted_le; autos*; try lia. }
        bool_rew; lia. }
    rewrite /R2.
    xin 2: fold'; xapp get_spec=> *...
    rewrite /R1.
    xapp get_spec_out_unary...
    { move/max_le; move: L2; rewrite take_ge ?length_List_length; try math.
      rewrite -/syind; lia. }
    xsimpl; try lia.
    splits*=> //.
    { move=> ?. suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia. }
    { move=> ?. suff: ind[l] < ind[l+1] by lia.
      apply/sorted_le; autos*; try lia. }
    bool_rew; lia. }
  { move=> ???. rewrite /ntriple -xnwp1_lemma /=.
    rewrite /Inv; xpull=> ix iy C.
    do ? (xwp; xapp). xapp @and.spec=> //.
    move=> ? E'; bool_rew; case: (C)=> ? [?][?][?][?][] ?.
    xsimpl=> // ?; subst; rewrite E' /cond. by bool_rew.  }
  { move=> ?? []/(_ eq_refl); by case: b. }
  { move=> *. move/NoDup_nthZ: ndind=> /[apply]; lia. }
  { move=> *. move/NoDup_nthZ: ndind=> /[apply]; lia. }
  { rewrite /arr1 /Inv/arrs/arr1; xsimpl lbx lby.
    { splits; [|lia|lia| | |autos*|].
      { rewrite /cond/ind; bool_rew; move: (size_merge sxind syind); lia. }
        { rewrite Z.sub_diag abs_0 /= max0=> ?.
          have: (In (nth 0 ind 0) ind) by apply/nth_In; lia.
          rewrite In_merge=> -[/xind_leq|/yind_leq]; lia. }
        { rewrite Z.sub_diag abs_0 /= max0=> ?.
          have: (In (nth 0 ind 0) ind) by apply/nth_In; lia.
          rewrite In_merge=> -[/xind_leq|/yind_leq]; lia. }
        rewrite /cond; bool_rew; do ? split; rewrite ?xindE ?yindE ?Z.sub_diag...
        { rewrite merge_nth0... }
        { move=> ?/(In_le_0 _ sorted_xind); rewrite -/sxind; lia. }
        move=> ?/(In_le_0 _ sorted_yind); rewrite -/syind; lia. }
    rewrite /H2/H1 ?E (fset_of_list_nodup 0) // /R1 /R2.
    rewrite -> ?hbig_fset_hstar; xsimpl*. }
  simpl=> v; rewrite /op/R1/R2/Inv/arr1/arrs/H2/H1 -fset_of_list_nodup //.
  rewrite -> ?hbig_fset_hstar; xsimpl=> ?? _ //. 
  do 4 (xwp; xapp); xwp; xval; xsimpl; rewrite /op.
  rewrite (@SumEq _ _
    (fun i => If ind i then v[`2](i) *  v[`3](i) else 0) 
    `[0, M]).
  { rewrite (SumIf' (fun=> id)) E (SumList 0) // Sum0s; f_equal; math. }
  by move=> ?; case: classicT.
Qed.

End sv.

End sv.