-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_CritChartEndMatrix.lean: instance decls only.
import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Instance.MvFormalGroup_CartierModuleWittAction
import Instance.MvFormalGroup_CartierModuleBaseChange
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Lemma.CerednikDrinfeld.CartierGradedPiece
import Lemma.CerednikDrinfeld.CriticalIndexChart
import Lemma.CerednikDrinfeld.CritChartEndMatrix

set_option autoImplicit false

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
