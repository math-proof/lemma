module

public import Mathlib.Topology.Algebra.Field
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Instance.ValuationSubring_CompletionDecompositionAction

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

variable (A : ValuationSubring (AlgebraicClosure ℚ))

def ratClosure : Subfield A.valuation.Completion :=
  (⊥ : Subfield A.valuation.Completion).topologicalClosure

end ValuationSubring

end
