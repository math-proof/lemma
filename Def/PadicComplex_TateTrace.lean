module

public import Mathlib
public import Instance.PadicComplex_GaloisAction

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

def towerClosure (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) : Set ℂ_[p] :=
  closure (⋃ m : ℕ, Set.range fun k : Km m => ((k : PadicAlgCl p) : ℂ_[p]))

end PadicComplex

end
