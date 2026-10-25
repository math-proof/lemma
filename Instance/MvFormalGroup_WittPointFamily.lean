-- Carved from Lemma/Definitions/Def_MvFormalGroup_WittPointFamily.lean: instance decls only.
import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Instance.MvFormalGroup_CartierModuleWittAction
import Lemma.MvFormalGroup.WittPointFamily

set_option autoImplicit false

noncomputable section

universe u v w

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace SeriesPoint

variable {d d' : ℕ} {R : Type u} [CommRing R] {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

instance instZero : Zero (SeriesPoint Φ τ) := ⟨SeriesPoint.zero⟩

instance instAdd : Add (SeriesPoint Φ τ) := ⟨SeriesPoint.add⟩

instance instNeg : Neg (SeriesPoint Φ τ) := ⟨SeriesPoint.neg⟩

instance instAddGroup : AddGroup (SeriesPoint Φ τ) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := SeriesPoint.ext (funext fun j =>
    subst_elim_assoc Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero c.constantCoeff_eq_zero j)
  zero_add a := SeriesPoint.ext (funext fun j => subst_elim_zero_left Φ a.constantCoeff_eq_zero j)
  add_zero a := SeriesPoint.ext (funext fun j => subst_elim_zero_right Φ a.constantCoeff_eq_zero j)
  neg_add_cancel a := SeriesPoint.ext (funext fun j =>
    subst_elim_negSeries_left Φ a.constantCoeff_eq_zero j)

instance instAddCommGroup [Φ.IsComm] : AddCommGroup (SeriesPoint Φ τ) :=
  { SeriesPoint.instAddGroup with
    add_comm := fun a b => SeriesPoint.ext (funext fun j =>
      subst_elim_comm Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero j) }

end SeriesPoint

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] {τ : Type v} {τ' : Type w}

variable {p}

variable (p R τ)

variable {p R τ}

instance charP_mvPowerSeries [CharP R p] : CharP (MvPowerSeries τ R) p :=
  charP_of_injective_ringHom (C_injective (σ := τ) (R := R)) p

end WittLaw


end MvFormalGroup

end
