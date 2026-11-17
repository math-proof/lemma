import Mathlib
import Def.FLTPrelim_Ramification

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

lemma liesOverPrime_comap_algEquiv_iff (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (q : ℕ) :
    (A.comap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).LiesOverPrime q ↔ A.LiesOverPrime q := by
  simp only [LiesOverPrime, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_natCast]

end ValuationSubring

namespace groupCohomology

open ValuationSubring

variable (S : Finset Nat.Primes)

def galoisSUnits : Subgroup (AlgebraicClosure ℚ)ˣ where
  carrier := {x | ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
    ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A}
  one_mem' A _ := by simp
  mul_mem' {x y} hx hy A hA := by
    obtain ⟨hx₁, hx₂⟩ := hx A hA
    obtain ⟨hy₁, hy₂⟩ := hy A hA
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact A.mul_mem _ _ hx₁ hy₁
    · rw [mul_inv_rev, Units.val_mul]; exact A.mul_mem _ _ hy₂ hx₂
  inv_mem' {x} hx A hA := by
    obtain ⟨hx₁, hx₂⟩ := hx A hA
    exact ⟨hx₂, by rwa [inv_inv]⟩

variable {S} in
lemma mem_galoisSUnits_iff (x : (AlgebraicClosure ℚ)ˣ) :
    x ∈ galoisSUnits S ↔ ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
      ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A :=
  Iff.rfl

end groupCohomology

end
