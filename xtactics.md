# Tactics to deal with ntriple/nwp

1. `LibSepReference.v`:
  - `xfocus l` : focuses on the `l`'s component
  - `xunfocus` : unfocuses the focused component 
  - `xin l : tac` : `xfocus l; tac; xunfocus` + some clean uo (recommended to use instead `xfocus`/`xunfocus`)
  - `xfocus l P` : focuses on the parts of `l`'s component that satisfies `P`
  - `xframe H` : frames out `H` form the precondition if the post condition has form `Q \* \Top`
  - `xnsimpl` : `xsimpl` for `ntriples` (use only if `xsimpl` fails)

2. `Loops.v`:
  - `xfor_sum Inv R R' op s` : applies `xfor_big_op_lemma` lemma with corresponded arguments

Enjoy!!