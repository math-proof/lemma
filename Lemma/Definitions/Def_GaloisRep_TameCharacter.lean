import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Algebra.Rat

namespace ValuationSubring

noncomputable def tameCharacter (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : IsLocalRing.ResidueField P := by
  classical
  exact if h : σ π / π ∈ P then IsLocalRing.residue P ⟨σ π / π, h⟩ else 0

end ValuationSubring
