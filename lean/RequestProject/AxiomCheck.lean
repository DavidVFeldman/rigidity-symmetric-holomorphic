import RequestProject.Main

/-!
# Compiled axiom audit

`#print axioms` for every load-bearing declaration of the development.
CI parses the build transcript produced by this file: each declaration must
report exactly the axioms `propext`, `Classical.choice`, `Quot.sound`, and
the transcript must contain no `sorryAx`. This is the semantic escape-hatch
check; no source text is grepped.
-/

open Rigidity

#print axioms AdmissiblyHolomorphic.diff_symm
#print axioms AdmissiblyHolomorphic.cesaro_vanish
#print axioms tail_vanish
#print axioms diff_vanishes_at_constant
#print axioms rigidity_along_c00
#print axioms rigidity_theorem
#print axioms rigidity_theorem_paper
#print axioms nosection_scalar
#print axioms nosection
#print axioms permAct_swap_moves_exceptional
#print axioms literal_statement_false
#print axioms exists_finPermBanachLimit
#print axioms connected_literal_statement_false
