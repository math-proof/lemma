module
public import Mathlib
public import Instance.MvFormalGroup_NegV2
public import Instance.MvFormalGroup_CartierModule
public import Instance.MvFormalGroup_CartierModuleWittAction
public import Instance.MvFormalGroup_CartierModuleBaseChange
public import Theorem.MvPowerSeries.SpecialFormalModule
public import Theorem.FormalGroup.CritChartEndMatrix
public import Def.FormalGroup_CritChartEndMatrix
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_CritChartEndMatrix.lean: instance decls only.

noncomputable section

universe u

namespace MvFormalGroup

namespace CartierModule

variable (p : ℕ) [hp : Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]

variable {p R}
variable {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

instance instModulePadicInt : Module ℤ_[p] (CartierModule p Φ) :=
  Module.compHom (CartierModule p Φ) (padicIntToWitt p R)

end CartierModule

end MvFormalGroup


end
