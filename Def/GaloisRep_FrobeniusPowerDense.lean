module

public import Mathlib
public import Instance.EllipticCurve_FrobeniusTrace
public import Def.FLTPrelim_Ramification

@[expose] public section

set_option autoImplicit false

def FrobeniusPowerDense (S : Finset ℕ)
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H
