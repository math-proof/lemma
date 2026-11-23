import Mathlib
import Def.FormalGroup_NegV2
import Def.FormalGroup_CartierModule
import Def.PowerSeries_CartierModuleHomothety
import Def.FormalGroup_CartierModuleWittAction
import Def.FormalGroup_CartierModuleBaseChange
import Def.CerednikDrinfeld_SpecialFormalModule
import Lemma.FormalGroup.CartierGradedPiece
import Def.CerednikDrinfeld_CriticalIndexChart
import Abbrev.CerednikDrinfeld_CritChartEndMatrix

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace CartierModule

variable (p : ℕ) [hp : Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]

def padicIntToWitt : ℤ_[p] →+* WittVector p R :=
  (WittVector.map (ZMod.castHom (dvd_refl p) R)).comp (WittVector.equiv p).symm.toRingHom

variable {p R}
variable {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

end CartierModule

end MvFormalGroup

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvPowerSeries.CartierModule MvPowerSeries PowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

variable [CharP B p]

namespace CritChart

def invariantsSubmodule (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    Submodule ℤ_[p] (CartierModule p X.F) where
  carrier := invariants X j i
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' z _ hm := smul_padicInt_mem_invariants j i z hm

def endODInvariantsLin (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) (f : endOD X) :
    Module.End ℤ_[p] (invariantsSubmodule X j i) where
  toFun m := ⟨endAct (f : MvFormalGroup.End X.F) m, endAct_mem_invariants j f.2 i m.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' z _ := Subtype.ext (endAct_smul_padicInt _ z _)

def endODInvariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    endOD X →+* Module.End ℤ_[p] (invariantsSubmodule X j i) where
  toFun := endODInvariantsLin X j i
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, OneMemClass.coe_one, map_one]; rfl)
  map_mul' f g := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, Subring.coe_mul, map_mul]; rfl)
  map_zero' := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, ZeroMemClass.coe_zero, map_zero]; rfl)
  map_add' f g := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, Subring.coe_add, map_add]; rfl)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def endMatrix (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) : endOD X →+* Matrix ι ι ℤ_[p] :=
  (LinearMap.toMatrixAlgEquiv β).toRingEquiv.toRingHom.comp (endODInvariants X j i)

def endMatrixQ (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) : endOD X →+* Matrix ι ι ℚ_[p] :=
  (algebraMap ℤ_[p] ℚ_[p]).mapMatrix.comp (endMatrix X j i β)

end CritChart

end FormalODModule

end CerednikDrinfeld

end
