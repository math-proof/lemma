-- Carved from Lemma/Definitions/Def_MvFormalGroup_PointsV2.lean: instance decls only.
import Instance.MvFormalGroup_NegV2
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Finiteness.Ideal
import Lemma.MvFormalGroup.PointsV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]


namespace Points

variable {F : MvFormalGroup g R} {S : Type*} [CommRing S] {J : Ideal S}

instance instZero : Zero (Points F S J) := ⟨⟨fun _ => 0, fun _ => Submodule.zero_mem _⟩⟩

variable [Algebra R S]

variable [IsAdicComplete J S]

instance instAdd : Add (Points F S J) := ⟨Points.add⟩

instance instNeg : Neg (Points F S J) := ⟨Points.neg⟩

instance instAddGroup : AddGroup (Points F S J) where
  add := (· + ·)
  zero := 0
  neg := fun x => -x
  add_assoc := Points.add_assoc
  zero_add := Points.zero_add
  add_zero := Points.add_zero
  neg_add_cancel := Points.neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instAddCommGroup [IsComm F] : AddCommGroup (Points F S J) :=
  { Points.instAddGroup with add_comm := Points.add_comm }

end Points


end MvFormalGroup
end
