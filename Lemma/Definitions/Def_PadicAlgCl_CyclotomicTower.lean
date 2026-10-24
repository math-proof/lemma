import Mathlib

set_option autoImplicit false

noncomputable section

namespace PadicAlgCl

def cyclotomicTower (p : ℕ) [Fact p.Prime] (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ n) = 1}

theorem mem_cyclotomicTower_of_pow_eq_one (p : ℕ) [Fact p.Prime] {n : ℕ} {ζ : PadicAlgCl p}
    (h : ζ ^ (p ^ n) = 1) : ζ ∈ cyclotomicTower p n :=
  IntermediateField.subset_adjoin ℚ_[p] _ h

theorem cyclotomicTower_mono (p : ℕ) [Fact p.Prime] : Monotone (cyclotomicTower p) := by
  intro m n hmn
  refine IntermediateField.adjoin.mono ℚ_[p] _ _ fun ζ (hζ : ζ ^ (p ^ m) = 1) => ?_
  show ζ ^ (p ^ n) = 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, pow_mul, hζ, one_pow]

end PadicAlgCl

end
