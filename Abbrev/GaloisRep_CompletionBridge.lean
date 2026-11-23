module

public import Mathlib
public import Def.FLTPrelim_Ramification

@[expose] public section

set_option autoImplicit false

open scoped NNReal Pointwise

variable (q : ℕ) [Fact q.Prime]

noncomputable abbrev padicIntegers : ValuationSubring (PadicAlgCl q) :=
  (Valued.v : Valuation (PadicAlgCl q) NNReal).valuationSubring

section Galois

end Galois
