-- Carved from Lemma/Definitions/Def_MvFormalGroup_CartierModule.lean: instance decls only.
import Mathlib
import Instance.MvFormalGroup_NegV2
import Lemma.MvFormalGroup.CartierModule

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace WittLaw

open MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime]

variable (R : Type u) [CommRing R]

instance instTendstoCofiniteProdMk (i : Fin 2) :
    Filter.TendstoCofinite (Prod.mk i : ℕ → Fin 2 × ℕ) :=
  Filter.tendstoCofinite_of_injective (Prod.mk_right_injective i)

variable {R}

end WittLaw

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

instance instZero : Zero (CartierModule p Φ) := ⟨CartierModule.zero Φ⟩

instance instAdd [Φ.IsComm] : Add (CartierModule p Φ) := ⟨CartierModule.add⟩

instance instNeg [Φ.IsComm] : Neg (CartierModule p Φ) := ⟨CartierModule.neg⟩

instance instAddCommGroup [Φ.IsComm] : AddCommGroup (CartierModule p Φ) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := CartierModule.ext (funext fun j =>
    subst_elim_assoc Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero c.constantCoeff_eq_zero j)
  zero_add a := CartierModule.ext (funext fun j =>
    subst_elim_zero_left Φ a.constantCoeff_eq_zero j)
  add_zero a := CartierModule.ext (funext fun j =>
    subst_elim_zero_right Φ a.constantCoeff_eq_zero j)
  add_comm a b := CartierModule.ext (funext fun j =>
    subst_elim_comm Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero j)
  neg_add_cancel a := CartierModule.ext (funext fun j =>
    subst_elim_negSeries_left Φ a.constantCoeff_eq_zero j)

end CartierModule


end MvFormalGroup

end
