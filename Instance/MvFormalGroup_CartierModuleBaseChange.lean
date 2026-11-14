-- Carved from Lemma/Definitions/Def_MvFormalGroup_CartierModuleBaseChange.lean: instance decls only.
import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.PowerSeries.CartierModuleHomothety
import Instance.MvFormalGroup_CartierModuleWittAction
import Lemma.MvPowerSeries.CartierModuleBaseChange

set_option autoImplicit false

noncomputable section

universe u v w

open MvPowerSeries

namespace MvFormalGroup

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ}
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {T : Type w} [CommRing T]

instance instIsCommMapRingHom (F : MvFormalGroup d R) [F.IsComm] (f : R →+* S) :
    (F.map f).IsComm :=
  isComm_map F f


end MvFormalGroup

end
