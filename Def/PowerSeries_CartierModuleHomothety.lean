module

public import Mathlib
public import Structure.MvFormalGroup_CartierModule

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

def teichFam (a : R) : ℕ → MvPowerSeries ℕ R := fun n => (a ^ p ^ n) • X n

end WittLaw

end MvFormalGroup

end
