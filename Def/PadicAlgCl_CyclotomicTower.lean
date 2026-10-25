import Mathlib

set_option autoImplicit false

noncomputable section

namespace PadicAlgCl

def cyclotomicTower (p : ℕ) [Fact p.Prime] (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ n) = 1}

end PadicAlgCl

end
