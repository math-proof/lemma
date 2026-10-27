import Structure.GaloisRep_Residual

open scoped TensorProduct

namespace ResidualGaloisRep

variable {k : Type} [Field k]

structure Equiv (ρ₁ ρ₂ : ResidualGaloisRep k) where

  toLinearEquiv : ρ₁.V ≃ₗ[k] ρ₂.V

  map_apply : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ρ₁.V),
    toLinearEquiv (ρ₁.ρ σ x) = ρ₂.ρ σ (toLinearEquiv x)


namespace Equiv


end Equiv

end ResidualGaloisRep
