import Mathlib

set_option autoImplicit false

noncomputable section

open MonoidWithZeroHom WithZeroTopology UniformSpace

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K) (F : Type*) [Field F] [Algebra F K]

def DecompositionIsometric : Prop :=
  ∀ (σ : A.decompositionSubgroup F) (x : K),
    A.valuation ((σ : K ≃ₐ[F] K) x) = A.valuation x

variable {A F}


section Completion

variable [h : Fact (A.DecompositionIsometric F)]


omit h in


def completionRingAut :
    A.decompositionSubgroup F →* (A.valuation.Completion ≃+* A.valuation.Completion) :=
  MulSemiringAction.toRingAut (A.decompositionSubgroup F) A.valuation.Completion

end Completion

end ValuationSubring

end
