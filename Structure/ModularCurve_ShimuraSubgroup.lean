module

public import Def.ModularCurve_HeckeModule
public import Theorem.MvPolynomial.HeckeModule

set_option autoImplicit false

public noncomputable section

namespace ModularCurve

def eisensteinNumerator (p : ℕ) : ℕ := (p - 1) / Nat.gcd (p - 1) 12

section MuType

variable (N : ℕ)

structure IsMuTypeJZeroSubgroup (S : AddSubgroup (JZero N)) : Prop where

  galoisStable : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ S, σ • x ∈ S

  galoisActsCyclotomic : ∀ (n : ℕ), ∀ x ∈ S, (n : ℤ) • x = 0 →
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (k : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ n = 1 → σ ζ = ζ ^ k) → σ • x = (k : ℤ) • x

structure IsShimuraSubgroup (S : AddSubgroup (JZero p)) : Prop where

  isMuType : IsMuTypeJZeroSubgroup p S

  hecke_eq : ∀ ℓ : Nat.Primes, ∀ x ∈ S, heckeOperatorBar p ℓ x = eisensteinSystem p ℓ • x

  card_eq : Nat.card ↥S = eisensteinNumerator p

end MuType
end ModularCurve
end
