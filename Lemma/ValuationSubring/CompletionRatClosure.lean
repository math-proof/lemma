import Mathlib.Topology.Algebra.Field
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Instance.ValuationSubring_CompletionDecompositionAction
import Def.ValuationSubring_CompletionRatClosure

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

variable (A : ValuationSubring (AlgebraicClosure ℚ))


theorem isClosed_ratClosure : IsClosed (ratClosure A : Set A.valuation.Completion) :=
  Subfield.isClosed_topologicalClosure _

theorem bot_le_ratClosure : (⊥ : Subfield A.valuation.Completion) ≤ ratClosure A :=
  Subfield.le_topologicalClosure _

theorem coe_ratClosure :
    (ratClosure A : Set A.valuation.Completion) = closure ((⊥ : Subfield A.valuation.Completion) : Set _) := rfl

@[simp] theorem ratCast_mem_ratClosure (q : ℚ) : (q : A.valuation.Completion) ∈ ratClosure A :=
  bot_le_ratClosure A (SubfieldClass.ratCast_mem _ q)

@[simp] theorem natCast_mem_ratClosure (n : ℕ) : (n : A.valuation.Completion) ∈ ratClosure A :=
  natCast_mem (ratClosure A) n

@[simp] theorem intCast_mem_ratClosure (n : ℤ) : (n : A.valuation.Completion) ∈ ratClosure A :=
  intCast_mem (ratClosure A) n

theorem coe_ratCast_mem_ratClosure (q : ℚ) :
    ((q : AlgebraicClosure ℚ) : A.valuation.Completion) ∈ ratClosure A := by
  have : ((q : AlgebraicClosure ℚ) : A.valuation.Completion) = (q : A.valuation.Completion) := by
    show (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion)
        ((WithVal.equiv A.valuation).symm (q : AlgebraicClosure ℚ)) = _
    rw [map_ratCast, map_ratCast]
  rw [this]; exact ratCast_mem_ratClosure A q

theorem coe_natCast_mem_ratClosure (n : ℕ) :
    ((n : AlgebraicClosure ℚ) : A.valuation.Completion) ∈ ratClosure A := by
  have : ((n : AlgebraicClosure ℚ) : A.valuation.Completion) = (n : A.valuation.Completion) := by
    show (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion)
        ((WithVal.equiv A.valuation).symm (n : AlgebraicClosure ℚ)) = _
    rw [map_natCast, map_natCast]
  rw [this]; exact natCast_mem_ratClosure A n

end ValuationSubring

end
