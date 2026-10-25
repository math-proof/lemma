import Mathlib.Topology.Algebra.Field
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Instance.ValuationSubring_CompletionDecompositionAction

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

variable (A : ValuationSubring (AlgebraicClosure ℚ))

def ratClosure : Subfield A.valuation.Completion :=
  (⊥ : Subfield A.valuation.Completion).topologicalClosure

end ValuationSubring

end
