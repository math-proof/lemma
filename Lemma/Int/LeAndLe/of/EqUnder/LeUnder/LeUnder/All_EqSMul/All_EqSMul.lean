import Mathlib
import sympy.Basic

open scoped Pointwise

/--
[Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant.lean)
-/
@[path]
private lemma main
  [Group G] [Finite G]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {𝔭₀ 𝔭₁ : Ideal B} [𝔭₀.IsPrime] [𝔭₁.IsPrime]
  {y : Ideal A} [y.IsPrime]
  {Q : Ideal B} [Q.IsPrime]
-- given
  (h₀ : ∀ g : G, g • 𝔭₀ = 𝔭₀)
  (h₁ : ∀ g : G, g • 𝔭₁ = 𝔭₁)
  (hy₀ : 𝔭₀.under A ≤ y)
  (hy₁ : 𝔭₁.under A ≤ y)
  (hQ : Q.under A = y) :
-- imply
  𝔭₀ ≤ Q ∧ 𝔭₁ ≤ Q := by
-- proof
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G

  have key : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (∀ g : G, g • 𝔭 = 𝔭) → 𝔭.under A ≤ y → 𝔭 ≤ Q := by
    intro 𝔭 _ hstab hle
    obtain ⟨Q', hQ'𝔭, hQ'prime, hQ'y⟩ := Ideal.exists_ideal_over_prime_of_isIntegral y 𝔭 hle
    have := hQ'prime

    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G Q' Q (by rw [hQ'y, hQ])
    rw [hg, ← hstab g]
    exact Ideal.pointwise_smul_le_pointwise_smul_iff.mpr hQ'𝔭
  exact ⟨key 𝔭₀ h₀ hy₀, key 𝔭₁ h₁ hy₁⟩


-- created on 2026-10-05
