Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibWP LibSepSimpl LibArray LibLoops Subst NTriple.
From LGTM.lib.theory Require Import LibListExt.
From LGTM.experiments Require Import Prelude UnaryCommon SV.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Module unordered_csr.

Import sv.

Section unordered_csr.

Notation "'mval'" := ("m_val":var) (in custom trm at level 0) : trm_scope.
Notation "'midx'" := ("m_idx":var) (in custom trm at level 0) : trm_scope.
Notation "'colind'" := ("col_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'rowptr'" := ("row_ptr":var) (in custom trm at level 0) : trm_scope.
Notation "'dvec'" := ("d_vec":var) (in custom trm at level 0) : trm_scope.
Notation "'lb'" := ("l_b":var) (in custom trm at level 0) : trm_scope.
Notation "'rb'" := ("r_b":var) (in custom trm at level 0) : trm_scope.
Notation "'i''" := ("i_'":var) (in custom trm at level 0) : trm_scope.

Import List Vars list_interval_notation.

Context (mval midx colind rowptr : list int).
Context (N Nrow Ncol Nidx : int).
Hypothesis Nrow_nonneg : 0 <= Nrow.
Hypothesis len_mval : length mval = N :> int.
Hypothesis len_midx : length midx = Nidx :> int.
Hypotheses Nidx_leq_Nrow : Nidx <= Nrow.
Hypothesis len_colind : length colind = N :> int.
Hypothesis len_rowptr : length rowptr = Nidx + 1 :> int.
Hypothesis colind_leq : forall x, In x colind -> 0 <= x < Ncol.
Hypothesis midx_leq : forall x, In x midx -> 0 <= x < Nrow.
Hypothesis rowptr_first : rowptr[0] = 0.
Hypothesis rowptr_last : rowptr[Nidx] = N.
Hypothesis rowptr_weakly_sorted : forall (i j : int), 
  (0 <= i <= Nidx) -> 
  (0 <= j <= Nidx) -> 
  (i <= j) -> 
  (rowptr[i] <= rowptr[j]).

Context (yind yval : list int).
Context (M : int).
Hypothesis len_xind : length yind = M :> int.
Hypothesis len_xval : length yval = M :> int.
Hypothesis stored_yind : sorted yind.
Hypothesis yind_leq : forall x, In x yind -> 0 <= x < Ncol.
Hypothesis Nrow0 : Nidx > 0. (* we get rid of it later *)

Definition colind_seg (row : int) := colind [[ (rowptr[row]) -- (rowptr[row + 1]) ]].

Hypothesis nodup_eachcol : forall x : int, 0 <= x < Nidx -> NoDup (colind_seg x).
Hypotheses nodup_midx : NoDup midx.

Tactic Notation "seclocal_solver" :=
  try (rewrite index_nodup=> //; math);
  first [ assumption 
    | rewrite -/(colind_seg _); now apply nodup_eachcol
    | (* for rowptr[?] <= N *)
      try rewrite -> len_colind; try rewrite -> len_mval; 
      try rewrite <- rowptr_last; apply rowptr_weakly_sorted; math
    | (* for 0 <= rowptr[?] *)
      rewrite <- rowptr_first at 1; apply rowptr_weakly_sorted; math
    | (* for 0 <= rowptr[i] <= rowptr[i + 1] *)
      split; [ rewrite <- rowptr_first at 1 | ]; apply rowptr_weakly_sorted; math
    | intros; eapply colind_leq, in_interval_list; now eauto
    | intros; now case_if
    | move=> >; rewrite -len_xind slice_fullE //
    | lia
    | intros; apply midx_leq, nth_In; math
    | idtac ]; auto.

Definition indexf := index.func Nidx.

Definition get (x_mval : loc) := 
<{
  fun midx colind rowptr i j =>
      let i = indexf i midx in
      let "i < Nidx" = i < Nidx in
      if "i < Nidx" then
        let lb = read_array rowptr i in
        let i' = i + 1 in
        let rb = read_array rowptr i' in
          sv.get j colind x_mval lb rb
      else 0
}>.

Lemma get_spec_out_unary {D : Type} `{Inhab D} (x_midx x_mval x_colind x_rowptr : loc) (i j : int) d :
  @htriple D (single d tt) 
    (fun=> get x_mval x_midx x_colind x_rowptr i j)
    (\[~ In i midx] \*
      harray_int mval x_mval d \* 
      harray_int midx x_midx d \* 
      harray_int colind x_colind d \* 
      harray_int rowptr x_rowptr d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      harray_int mval x_mval d \* 
      harray_int midx x_midx d \* 
      harray_int colind x_colind d \* 
      harray_int rowptr x_rowptr d).
Proof with seclocal_solver.
  xwp; xsimpl; intros Hnotin%memNindex; xapp @index.spec... 
  xwp; xapp. xwp; xif=> HQ; try math.
  xwp; xval. xsimpl*.
Qed.

Lemma get_spec_out `{Inhab (labeled (int * int))} fs (x_midx x_mval x_colind x_rowptr : loc) : 
  @htriple (labeled (int * int)) fs
    (fun d => get x_mval x_midx x_colind x_rowptr (eld d).1 (eld d).2)
    (\[forall d, indom fs d -> ~ In (eld d).1 midx] \*
      (\*_(d <- fs) harray_int mval x_mval d) \* 
      (\*_(d <- fs) harray_int midx x_midx d) \* 
      (\*_(d <- fs) harray_int colind x_colind d) \* 
       \*_(d <- fs) harray_int rowptr x_rowptr d)
    (fun hr => 
     \[hr = fun=> 0] \* 
      (\*_(d <- fs) harray_int mval x_mval d) \*
      (\*_(d <- fs) harray_int midx x_midx d) \* 
      (\*_(d <- fs) harray_int colind x_colind d) \*  
       \*_(d <- fs) harray_int rowptr x_rowptr d).
Proof. by xpointwise_build (@get_spec_out_unary). Qed.

Definition sum := 
  <{
    fun mval midx colind rowptr =>
    let s = ref 0 in
    for i <- [0, Nidx] {
      let lb = read_array rowptr i in
      let i' = i + 1 in
      let rb = read_array rowptr i' in
      let x = sv.sum colind mval lb rb in 
        s += x
    };
    ! s
}>.

Tactic Notation "seclocal_fold" := 
  rewrite ?label_single ?wp_single
    -/(For_aux _ _) 
    -/(For _ _ _) //=.

Local Notation Dom := (int * int)%type.
Local Notation D := (labeled (int * int)).
Definition eld := @LibWP.eld (int * int)%type.
Coercion eld : D >-> Dom.

Lemma sum_spec `{Inhab D} `{Inhab (labeled int)} (x_mval x_colind x_rowptr x_midx : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_midx, midx)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_midx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}   => sum x_mval x_midx x_colind x_rowptr];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_midx x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Nrow] \x `[0, Ncol]) hv[`2](i)] \* \Top}}.
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus* (2,0) (indom (midx \x `[0, Ncol])).
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap.
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  xin (1,0) : xwp; xapp=> s...
  xfor_sum Inv R R (fun hv i => Σ_(j <- `{midx[i]} \x `[0, Ncol]) hv[`2](j)) s.
  { xin (2,0) : rewrite wp_prod_single /=.
    xin (1,0) : do 3 (xwp; xapp)...
    xsubst (snd : _ -> int).
    xfocus (2,0); rewrite -> ! hbig_fset_hstar.
    xwp; xapp (@index.Spec `[0, Ncol] Nidx (2,0) midx x_midx (fun=> midx[l0]))=> //.
    rewrite index_nodup //; try math.
    xwp; xapp. xwp; xif=> ?; [ | math ].
    do 3 (xwp; xapp).
    xunfocus; xin (1,0) : idtac. (* reformat *)
    xnapp sv.sum_spec...
    xsimpl=>->. xapp @incr.spec. rewrite sum_prod1E. xsimpl. }
  { move=>Ha Hb Hc; left. move: Ha; apply contrapose, NoDup_nthZ; autos*; math. }
  xwp; xapp. xsimpl*. xsum_normalize.
  rewrite SumCascade -?prod_Union_distr -?len_midx -?(fset_of_list_nodup 0) ?E //.
  disjointE.
  move=>Ha Hb Hc; left. move: Ha; apply contrapose, NoDup_nthZ; autos*; math.
Qed.

Context (dvec : list int).
Context (dvec_len : length dvec = Ncol :> int).

(* challenge: unordered array set *)
Definition spmv := 
  <{
  fun mval midx colind rowptr dvec =>
  let s = alloc0 Nrow in
  for i <- [0, Nidx] {
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
    let i = read_array midx i in
    let x = sv.dotprod colind mval dvec lb rb in 
    val_array_set s i x
  }; 
  s
}>.

Ltac xstep := xwp; xapp.
Ltac xgo := do ? xstep.
Tactic Notation "xapp*" constr(E) := xwp; xapp_big E=> //.
Tactic Notation "xin*" constr(S1) ":" tactic(tac) := 
  let n := constr:(S1) in
  xfocus n; try rewrite wp_prod_single /=; tac; try(
  first [xunfocus | xcleanup n]; simpl; try apply xnwp0_lemma); rewrite -?xntriple1_lemma /=.

Tactic Notation "xmalloc" ident(s) := xwp; xapp (@htriple_alloc0_unary)=> // s.

Hint Resolve lhtriple_array_set_pre : lhtriple.

Lemma spmv_spec `{Inhab D} `{H__ : Inhab (labeled int)} (x_mval x_midx x_colind x_rowptr x_dvec : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_midx, midx)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     arr(x_dvec, dvec)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_midx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_dvec, dvec)⟨2, i⟩) }}
  [{
    [1| ld in `{(0,0)}                 => spmv x_mval x_midx x_colind x_rowptr x_dvec];
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_midx x_colind x_rowptr ld.1 ld.2}
  }]
  {{ hv,
    harray_fun_int (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * dvec[j]) (hv[`1]((0,0))) Nrow (Lab (1,0) (0,0))
      \* \Top }}.
Proof with (try seclocal_fold; seclocal_solver).
  xset_Inv Inv 1; xset_R int Inv R 2.
  xfocus* (2,0) (indom (midx \x `[0, Ncol])).
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap.
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  xin (1,0) : xmalloc ans...
  xfor_arrayset Inv R R 
    (fun hv (i : int) => (If (In i midx) then Σ_(j <- `{i} \x `[0, Ncol]) (hv[`2](j) * dvec[j.2]) else 0)) 
    (fun _ : int => 0) ans midx...
  { xin* (2,0): xapp* @index.specs; xstep; xwp; xif=> [?|]; xgo...
    xin (1,0) : xgo...
    rewrite index_nodup //; try math.
    xsubst (snd : _ -> int).
    xnapp sv.dotprod_spec...
    xsimpl=>->; xapp; rewrite sum_prod1E; xsimpl.
    case: classicT=> [?|/(_ (nth_In _ _ _))] //; lia. }
  xwp; xval. xsimpl*. erewrite -> harray_fun_int_congr; try assumption; first xsimpl*.
  move=> i Hi /=. xsum_normalize.
  case_if.
  { rewrite sum_prod1E /=; apply SumEq=> >; indomE.
    case: classicT=> // /[swap]? []; exists (index i midx); indomE=> /=.
    splits; try tauto. 
    { rewrite -len_midx index_mem //; splits*; exact/(indexG0). }
    { by rewrite nth_index. } }
  { rewrite -> SumEq with (G:=fun=> 0)=> [|?]; first by rewrite Sum0s.
    indomE; case: classicT=> // -[?]; indomE=> /=-[?][*]. 
    case: C; subst; apply/nth_In; math. }
Qed.



Hypothesis sorted_eachcol : forall x : int, 0 <= x < Nidx -> sorted (colind_seg x).

Definition spmspv x_colind y_ind x_mval y_val := 
  let dot := sv.sv_dotprod x_colind y_ind x_mval y_val in
  <{
  fun rowptr midx =>
  let s = alloc0 Nrow in
  for i <- [0, Nidx] {
    let lb = read_array rowptr i in
    let i' = i + 1 in
    let rb = read_array rowptr i' in
    let i = read_array midx i in
    let x = dot lb rb 0 M in 
      val_array_set s i x
  }; 
  s
}>.

Lemma ntriple_frame_array D H fs_ht H' 
  (fs : list int) (p : loc) f g d S : 
  (forall i, In i fs -> 0 <= i < S) ->
  (forall i v, ~ In i fs -> f i = g v i) ->
  (H = H' (harray_fun_int f p S d)) ->
  (forall X, H' X = (H' hempty) \* X) ->
  H' (\*_(i <- fs) (p + 1 + abs i)%nat ~(d)~> f i) ==> 
    nwp fs_ht (fun (v : labeled D -> val) => (\*_(i <- fs) (p + 1 + abs i)%nat ~(d)~> g v i) \* \Top) ->
  ntriple H fs_ht (fun hv => (harray_fun_int (g hv) p S d) \* \Top).
Proof.
Admitted.


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
Admitted.

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
|intro; xcleanup (1,0); exact: himpl_refl]; rewrite -wp_equiv /=.

Tactic Notation "xin" constr(S1) ":" tactic(tac) := 
  let n := constr:(S1) in
  xfocus n; tac; try(
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

Lemma hbig_fset_list (fs : list int) :
    NoDup fs ->
    @hbig_fset D int hstar fs = 
    fun (H : _ -> hhprop D) =>
    \*_(i <- `[0,length fs]) H (fs[i]).
Proof.
Admitted.

Hint Rewrite hbig_fset_list : hstar_fset.

Notation size := length.

Lemma spmspv_spec `{Inhab D} `{H__ : Inhab (labeled int)}
  (x_mval x_colind x_midx x_rowptr y_ind y_val : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_midx, midx)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     arr(y_ind, yind)⟨1, (0,0)⟩ \* 
     arr(y_val, yval)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_midx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, Nrow] \x `[0, Ncol]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_ind, yind)⟨3, i⟩) \* 
     (\*_(i <- `{0} \x `[0, Ncol]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    {1| ld in `{(0,0)}                 => spmspv x_colind y_ind x_mval y_val x_rowptr x_midx};
    {2| ld in `[0, Nrow] \x `[0, Ncol] => get x_mval x_midx x_colind x_rowptr ld.1 ld.2};
    {3| ld in `{0}       \x `[0, Ncol] => sv.get ld.2 y_ind y_val 0 M}
  }]
  {{ hv,
    harray_fun_int (fun i => Σ_(j <- `[0, Ncol]) hv[`2]((i, j)) * hv[`3]((0, j))) (hv[`1]((0,0))) Nrow (Lab (1,0) (0,0))
      \* \Top }}.
Proof with (try seclocal_fold; seclocal_solver; autos* ).
  xstart.
  xfocus* (2,0) (indom (midx \x `[0, Ncol])).
  xapp get_spec_out=> //. 1: case=> ??; indomE; tauto.
  xclean_heap.
  xin (1,0) : xmalloc p=> //; xret...
  xframe_array p midx...
  { move=> *; erewrite <-Sum0s at 1; apply/SumEq=> ?.
    indomE=> /=; case_if... }
  have E : (`[0, Nrow] \x `[0, Ncol]) ∩ indom (midx \x `[0, Ncol]) = midx \x `[0, Ncol].
  { rewrite -prod_intr_list_on_1. f_equal. now apply intr_list. }
  rewrite E (fset_of_list_nodup 0 nodup_midx) len_midx prod_Union_distr.
  rewrite -(Union_same Nidx (`{0} \x `[0, Ncol])) //; try math.
  xfor_bigsrt Inv R2 R3
    (fun l => (p + 1 + abs midx[l])%nat ~⟨(1%Z, 0%Z), (0, 0)⟩~> 0) 
    (fun l hv => (p + 1 + abs midx[l])%nat ~⟨(1%Z, 0%Z), (0, 0)⟩~>  
      Σ_(j <- `[0, Ncol]) hv[`2]((midx[l], j)) * hv[`3]((0, j))).
  { xin* (2,0): xapp* @index.specs; xstep; xwp; xif=> [?|]; xgo...
    xin (1,0) : xgo...
    rewrite index_nodup //; try math.
    xsubst (snd : _ -> int).
    xnapp sv.sv_dotprod_spec... 
    xsimpl=>->; xapp; xsimpl. }
  erewrite hbig_fset_eq with (fs := `[0, Nidx]); first xsimpl*.
  move=> ?; indomE=> ?; do 2? f_equal; apply/SumEq=> ?.
  rewrite -prod_Union_distr -len_midx -fset_of_list_nodup; indomE=> //=.
  rewrite -index_mem index_nodup; try case_if...
Qed. 

End unordered_csr.

End unordered_csr.
