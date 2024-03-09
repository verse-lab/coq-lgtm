# LGTM triples in Coq

Here we discuss how the Coq encoding of LGTM triples is different from the paper one. For illustration, purposes we consider the example from the section 4 (Fig. 13). The Coq embedding LGTM triple looks like

```coq
Lemma spmspv_spec `{Inhab D} `{H__ : Inhab (labeled int)}
  (x_mval x_colind x_midx x_rowptr y_ind y_val : loc) : 
  {{ arr(x_mval, mval)⟨1, (0,0)⟩ \*
     arr(x_midx, midx)⟨1, (0,0)⟩ \*
     arr(x_colind, colind)⟨1, (0,0)⟩ \*
     arr(x_rowptr, rowptr)⟨1, (0,0)⟩ \*
     arr(y_ind, yind)⟨1, (0,0)⟩ \* 
     arr(y_val, yval)⟨1, (0,0)⟩ \* 
     (\*_(i <- `[0, N] \x `[0, M]) arr(x_mval, mval)⟨2, i⟩) \*
     (\*_(i <- `[0, N] \x `[0, M]) arr(x_midx, midx)⟨2, i⟩) \*
     (\*_(i <- `[0, N] \x `[0, M]) arr(x_colind, colind)⟨2, i⟩) \*
     (\*_(i <- `[0, N] \x `[0, M]) arr(x_rowptr, rowptr)⟨2, i⟩) \*
     (\*_(i <- `{0} \x `[0, M]) arr(y_ind, yind)⟨3, i⟩) \* 
     (\*_(i <- `{0} \x `[0, M]) arr(y_val, yval)⟨3, i⟩) }}
  [{
    {1| _  in `{(0,0)}           => spmspv x_colind y_ind x_mval y_val x_rowptr x_midx};
    {2| ij in `[0, N] \x `[0, M] => get x_mval x_midx x_colind x_rowptr ij.1 ij.2};
    {3| j  in `{0}    \x `[0, M] => sv.get j.2 y_ind y_val 0 M}
  }]
  {{ hv,
    arrf(hv[`1]((0,0)), i in N => Σ_(j <- `[0, M]) hv[`2]((i, j)) * hv[`3]((0, j)))⟨1, (0,0)⟩
      \* \Top }}.
```

Major differences with the paper verison are: 
1. The Coq notation for `x(i) |-> y` heap predicate is `x |-(i)-> y`. 
2. The Coq notation for `arr(x(i), y)` heap predicate is `arr(x, y)⟨i⟩`. `arrf(x, i in N => f(i))⟨i⟩` from the post condition is a syntactic sugar to `arr(x, [f(0), f(1),.., f(N-1)])⟨i⟩`. 
3. The triple from the paper has three index sets for each product program: 
  - $\{⟨1,0⟩\}$: stands for $\{0\}$ set with tag `1`
  - $\{⟨2, i, j⟩ : i \in [0,M), j \in [0,N) \}$: stands for $[0,M)\times[0,N)$ with tag `2`
  - $\{⟨3, i⟩ : i \in  [0,N) \}$: stands for $[0,N)$ with tag `3`
  In Coq, within one triple we only support index sets of the same type (different triples can have index sets of different types). That is why the first and the third index set of the Coq triple have an artificial extra component (which is always `0`). The type of index set elements in this case would be `labeled (int * int)`, where `labeled T` is a type of elements from `T` paired with some tag.
4. In the paper the output of each component is a separate hyper value. Here all 
  outputs are assembled in the one hyper value `hv`. To reference to the outcome of
  each particular component with tag `t`, one should write `hv['t]`.


# Other variations of LGTM triples

Other equivalent variations of LGTM triple embeddings include 

```coq
htriple fs code Pre Post
```
and 
```coq
Pre ==> wp fs code Post
```
Where `fs` is a finite index set, `code` is a function from the index set to program ASTs, `Pre` is a precondition and `Post` is a postcondition.
