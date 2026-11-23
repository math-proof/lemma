module

public import Mathlib
public import Theorem.MvPowerSeries.NegV2
public import Theorem.MvPowerSeries.CartierModule
public import Theorem.PowerSeries.CartierModuleTeichFam
public import Def.PowerSeries_Homothety

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}


public theorem homothety_eq_precomp [Φ.IsComm] (a : R) :
    (homothety a : CartierModule p Φ →+ CartierModule p Φ) = precomp (WittLaw.isEndo_teichFam a) :=
  rfl


@[simp] public theorem toPowerSeries_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    (homothety a f).toPowerSeries = fun j => subst (WittLaw.teichFam p a) (f.toPowerSeries j) := rfl


public theorem toPowerSeries_homothety_eq_rescale [Φ.IsComm] (a : R) (f : CartierModule p Φ) (j : Fin d) :
    (homothety a f).toPowerSeries j = rescale (fun n => a ^ p ^ n) (f.toPowerSeries j) :=
  WittLaw.subst_teichFam a _


public theorem coeff_toPowerSeries_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) (j : Fin d)
    (e : ℕ →₀ ℕ) :
    coeff e ((homothety a f).toPowerSeries j) =
      (e.prod fun n k => (a ^ p ^ n) ^ k) * coeff e (f.toPowerSeries j) := by
  rw [toPowerSeries_homothety_eq_rescale, coeff_rescale]


public theorem homothety_one [Φ.IsComm] (f : CartierModule p Φ) : homothety (1 : R) f = f := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_homothety, WittLaw.teichFam_one]
  exact congrFun subst_self _


public theorem homothety_zero_left [Φ.IsComm] (f : CartierModule p Φ) : homothety (0 : R) f = 0 := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_homothety, WittLaw.teichFam_zero]
  exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j)


public theorem homothety_mul [Φ.IsComm] (a b : R) (f : CartierModule p Φ) :
    homothety (a * b) f = homothety a (homothety b f) := by
  apply CartierModule.ext
  funext j
  show (precomp _ f).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, toPowerSeries_precomp]
  show subst (WittLaw.teichFam p (a * b)) (f.toPowerSeries j) = _
  congr 1
  funext n
  rw [WittLaw.subst_teichFam_teichFam]


public theorem homothety_comm [Φ.IsComm] (a b : R) (f : CartierModule p Φ) :
    homothety a (homothety b f) = homothety b (homothety a f) := by
  rw [← homothety_mul, mul_comm, homothety_mul]


public theorem homothety_verschiebung [Φ.IsComm] [CharP R p] (a : R) (f : CartierModule p Φ) :
    homothety a (verschiebung f) = verschiebung (homothety (a ^ p) f) := by
  apply CartierModule.ext
  funext j
  show (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact WittLaw.subst_teichFam_frobFam a n


public theorem frobenius_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    frobenius (homothety a f) = homothety (a ^ p) (frobenius f) := by
  apply CartierModule.ext
  funext j
  show (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact (WittLaw.subst_teichFam_verFam a n).symm


public theorem homothety_nsmul [Φ.IsComm] (a : R) (n : ℕ) (f : CartierModule p Φ) :
    homothety a (n • f) = n • homothety a f :=
  map_nsmul _ _ _


public theorem map_homothety [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (a : R) (f : CartierModule p Φ) :
    map φ (homothety a f) = homothety a (map φ f) :=
  map_precomp φ _ f


public theorem endAct_homothety [Φ.IsComm] (φ : MvFormalGroup.End Φ) (a : R) (f : CartierModule p Φ) :
    endAct φ (homothety a f) = homothety a (endAct φ f) :=
  map_precomp φ _ f


public theorem tangent_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    tangent (homothety a f) = a • tangent f := by
  funext j
  rw [tangent_apply, coeff_toPowerSeries_homothety, Pi.smul_apply, tangent_apply, smul_eq_mul,
    Finsupp.prod_single_index (by simp), pow_zero, pow_one, pow_one]


public theorem curve_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) (j : Fin d) :
    curve (homothety a f) j = PowerSeries.rescale a (curve f j) := by
  rw [curve_apply, toPowerSeries_homothety, curve_apply,
    subst_comp_subst_apply (WittLaw.hasSubst_teichFam a) hasSubst_curveFam,
    PowerSeries.rescale_eq, rescale_eq_subst,
    subst_comp_subst_apply hasSubst_curveFam (HasSubst.smul_X _)]
  congr 1
  funext n
  rw [WittLaw.subst_curveFam_teichFam, PowerSeries.rescale_eq, rescale_eq_subst]

namespace Examples


public theorem homothety_addLinear (a : R) (v : Fin d → R) :
    homothety a (addLinear p v) = addLinear p (a • v) := by
  apply CartierModule.ext
  funext i
  rw [toPowerSeries_homothety, toPowerSeries_addLinear]
  show subst (WittLaw.teichFam p a) ((addLinear p v).toPowerSeries i) = _
  rw [toPowerSeries_addLinear, subst_smul (WittLaw.hasSubst_teichFam a),
    subst_X (WittLaw.hasSubst_teichFam a), WittLaw.teichFam_apply, pow_zero, pow_one, smul_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm]

end Examples

end CartierModule

end MvFormalGroup

end
