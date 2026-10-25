import Def.LocalLanglands_LocalHeckeInstance

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable (p : ℕ) [Fact p.Prime]

def IsUnramified (μ : ℚ_[p]ˣ →* ℂˣ) : Prop :=
  ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 → μ u = 1


def unitValuation : ℚ_[p]ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (u : ℚ_[p]).valuation
  map_one' := by simp [Padic.valuation_one]
  map_mul' u v := by
    simp only [Units.val_mul]
    rw [Padic.valuation_mul u.ne_zero v.ne_zero, ofAdd_add]


def valChar (s : ℂˣ) : ℚ_[p]ˣ →* ℂˣ :=
  (zpowersHom ℂˣ s).comp (unitValuation p)


def higherUnits (n : ℕ) : Set ℚ_[p]ˣ :=
  {u | ‖(u : ℚ_[p])‖ = 1 ∧ (n = 0 ∨ ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)))}


def HasCharConductor (μ : ℚ_[p]ˣ →* ℂˣ) (c : ℕ) : Prop :=
  (∀ u ∈ higherUnits p c, μ u = 1) ∧ ∀ m < c, ∃ u ∈ higherUnits p m, μ u ≠ 1

end LocalNewvector

end
