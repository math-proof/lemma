import Mathlib
import Lemma.Definitions.Def_ModularCurve_PDPairing

set_option autoImplicit false

namespace ModularCurve.CupPairing

open scoped MatrixGroups

def IsPrimitive {G : Type*} [Group G] {R : Type*} [CommRing R] (φ ψ : Additive G →+ R)
    (h : G → R) : Prop :=
  ∀ g g' : G, h (g * g') = h g + h g' - ModularCurve.PDPairing.omega φ ψ g g'

noncomputable def mult (Γ : Subgroup SL(2, ℤ)) : ℚ := by
  classical
  exact if (-1 : SL(2, ℤ)) ∈ Γ then 1 else 2

noncomputable def pair (Γ : Subgroup SL(2, ℤ)) (φ ψ : Additive Γ →+ ℚ) : ℚ := by
  classical
  exact if hΓ : Γ.FiniteIndex then
      if hp : ∃ h : Γ → ℚ, IsPrimitive φ ψ h then
        (@ModularCurve.PDPairing.cuspSum Γ hΓ ℚ _ (Classical.choose hp)) / (2 * mult Γ)
      else 0
    else 0

theorem pair_eq_dif (Γ : Subgroup SL(2, ℤ)) [hΓ : Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ)
    (hp : ∃ h : Γ → ℚ, IsPrimitive φ ψ h) :
    pair Γ φ ψ = ModularCurve.PDPairing.cuspSum Γ (Classical.choose hp) / (2 * mult Γ) := by
  unfold pair
  rw [dif_pos hΓ, dif_pos hp]

theorem pair_eq_zero_of_not_exists (Γ : Subgroup SL(2, ℤ)) (φ ψ : Additive Γ →+ ℚ)
    (hp : ¬ ∃ h : Γ → ℚ, IsPrimitive φ ψ h) : pair Γ φ ψ = 0 := by
  unfold pair
  split_ifs <;> rfl

theorem pair_eq_zero_of_not_finiteIndex (Γ : Subgroup SL(2, ℤ)) (φ ψ : Additive Γ →+ ℚ)
    (hΓ : ¬ Γ.FiniteIndex) : pair Γ φ ψ = 0 := by
  unfold pair
  rw [dif_neg hΓ]

theorem mult_ne_zero (Γ : Subgroup SL(2, ℤ)) : mult Γ ≠ 0 := by
  unfold mult
  split_ifs <;> norm_num

end ModularCurve.CupPairing
