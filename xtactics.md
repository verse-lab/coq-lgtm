# Tactics to deal with ntriple/nwp

1. `LibSepReference.v`:
  - `xfocus l` : focuses on the `l`'s component
  - `xunfocus` : unfocuses the focused component 
  - `xin l : tac` : `xfocus l; tac; xunfocus` + some clean up (recommended to use instead `xfocus`/`xunfocus`)
  - `xfocus l P` : focuses on the parts of `l`'s component that satisfies `P`
  - `xframe H` : frames out `H` form the precondition if the post condition has form `Q \* \Top`
  - `xnsimpl` : `xsimpl` for `ntriples` (use only if `xsimpl` fails)

2. `Loops.v`:
  - `xfor_sum Inv R R' op s` : applies `xfor_big_op_lemma` lemma with corresponded arguments. This tactic is applicable for goals of the form:
  ```
  {{ H }}
  [{
    [i: ld in `{_} => for i <- [0, N] { C1 }; C2]
    [j: ld in S    => C3]
  }]
  {{ Q }}
  ```
     

Enjoy!!