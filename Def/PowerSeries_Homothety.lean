module

public import Mathlib
public import Def.FormalGroup_CartierModule
public import Theorem.PowerSeries.CartierModuleTeichFam

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R}

def homothety [Φ.IsComm] (a : R) : CartierModule p Φ →+ CartierModule p Φ :=
  precomp (WittLaw.isEndo_teichFam a)

end CartierModule

end MvFormalGroup

end
