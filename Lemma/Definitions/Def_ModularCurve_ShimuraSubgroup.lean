import Lemma.Definitions.Def_ModularCurve_HeckeModule
import Lemma.Definitions.Def_ModularCurve_ModularUnit

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section MuType

variable (N : ℕ)

structure IsMuTypeJZeroSubgroup (S : AddSubgroup (JZero N)) : Prop where

  galoisStable : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ S, σ • x ∈ S

  galoisActsCyclotomic : ∀ (n : ℕ), ∀ x ∈ S, (n : ℤ) • x = 0 →
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (k : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ n = 1 → σ ζ = ζ ^ k) → σ • x = (k : ℤ) • x

theorem isMuTypeJZeroSubgroup_bot : IsMuTypeJZeroSubgroup N ⊥ where
  galoisStable := fun σ x hx => by
    obtain rfl : x = 0 := AddSubgroup.mem_bot.mp hx
    exact AddSubgroup.mem_bot.mpr (@smul_zero _ (JZero N) _ _ σ)
  galoisActsCyclotomic := fun n x hx _ σ k _ => by
    obtain rfl : x = 0 := AddSubgroup.mem_bot.mp hx
    exact (@smul_zero _ (JZero N) _ _ σ).trans (smul_zero (k : ℤ)).symm

end MuType

section Shimura

variable (p : ℕ) [Fact p.Prime]

structure IsShimuraSubgroup (S : AddSubgroup (JZero p)) : Prop where

  isMuType : IsMuTypeJZeroSubgroup p S

  hecke_eq : ∀ ℓ : Nat.Primes, ∀ x ∈ S, heckeOperatorBar p ℓ x = eisensteinSystem p ℓ • x

  card_eq : Nat.card ↥S = eisensteinNumerator p

theorem isShimuraSubgroup_bot_of_eisensteinNumerator_eq_one
    (hp : eisensteinNumerator p = 1) : IsShimuraSubgroup p ⊥ where
  isMuType := isMuTypeJZeroSubgroup_bot p
  hecke_eq := fun ℓ x hx => by
    rw [AddSubgroup.mem_bot] at hx
    rw [hx, map_zero, smul_zero]
  card_eq := by rw [hp, AddSubgroup.card_bot]

example : @IsShimuraSubgroup 13 ⟨by decide⟩ ⊥ :=
  @isShimuraSubgroup_bot_of_eisensteinNumerator_eq_one 13 ⟨by decide⟩ (by decide)

end Shimura

end ModularCurve
