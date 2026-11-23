module

public import Mathlib
public import Theorem.MvPowerSeries.NegV2
public import Theorem.MvPowerSeries.CartierModule
public import Def.PowerSeries_CartierModuleHomothety

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

@[simp] public theorem teichFam_apply (a : R) (n : ℕ) : teichFam p a n = (a ^ p ^ n) • X n := rfl

omit hp in

public theorem teichFam_eq_smul_X (a : R) :
    teichFam p a = (fun n => a ^ p ^ n) • (X : ℕ → MvPowerSeries ℕ R) := rfl

omit hp in

public theorem constantCoeff_teichFam (a : R) (n : ℕ) : (teichFam p a n).constantCoeff = 0 := by
  rw [teichFam_apply, smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]

omit hp in

public theorem hasSubst_teichFam (a : R) : HasSubst (teichFam p a) := HasSubst.smul_X _

omit hp in


public theorem subst_teichFam (a : R) (f : MvPowerSeries ℕ R) :
    subst (teichFam p a) f = rescale (fun n => a ^ p ^ n) f :=
  (rescale_eq_subst _ f).symm

omit hp in


public theorem pairFam_teichFam (a : R) :
    pairFam (teichFam p a) = (fun im : Fin 2 × ℕ => a ^ p ^ im.2) • X := by
  funext ⟨i, m⟩
  rw [pairFam_apply, teichFam_apply, subst_smul (hasSubst_blk i), subst_X (hasSubst_blk i)]
  rfl


public theorem isEndo_teichFam (a : R) : IsEndo p (teichFam p a) := by
  refine ⟨hasSubst_teichFam a, constantCoeff_teichFam a, fun n => ?_⟩
  rw [teichFam_apply, subst_smul (hasSubst_addFam p R), subst_X (hasSubst_addFam p R),
    pairFam_teichFam, ← rescale_eq_subst]
  ext e
  rw [coeff_smul, coeff_rescale]
  by_cases he : coeff e (addFam p R n) = 0
  · rw [he, mul_zero, mul_zero]
  · congr 1
    rw [← weight_eq_of_coeff_addFam_ne_zero p R he, Finsupp.weight_apply, Finsupp.prod,
      Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun im _ => ?_
    rw [← pow_mul, weight_apply, one_mul, smul_eq_mul, mul_comm]

omit hp in


public theorem teichFam_one : teichFam p (1 : R) = X := by
  funext n
  rw [teichFam_apply, one_pow, one_smul]


public theorem teichFam_zero : teichFam p (0 : R) = 0 := by
  funext n
  rw [teichFam_apply, zero_pow (pow_ne_zero n hp.out.ne_zero), zero_smul, Pi.zero_apply]

omit hp in


public theorem subst_teichFam_teichFam (a b : R) (n : ℕ) :
    subst (teichFam p a) (teichFam p b n) = teichFam p (a * b) n := by
  rw [teichFam_apply, subst_smul (hasSubst_teichFam a), subst_X (hasSubst_teichFam a),
    teichFam_apply, teichFam_apply, smul_smul, mul_pow, mul_comm]


public theorem subst_teichFam_frobFam (a : R) (n : ℕ) :
    subst (teichFam p a) (frobFam p R n) = subst (frobFam p R) (teichFam p (a ^ p) n) := by
  rw [frobFam_apply, subst_pow (hasSubst_teichFam _), subst_X (hasSubst_teichFam _), teichFam_apply,
    smul_pow, teichFam_apply, subst_smul hasSubst_frobFam, subst_X hasSubst_frobFam, frobFam_apply,
    ← pow_mul, ← pow_mul, mul_comm (p ^ n) p]

omit hp in


public theorem subst_teichFam_verFam (a : R) (n : ℕ) :
    subst (teichFam p (a ^ p)) (verFam R n) = subst (verFam R) (teichFam p a n) := by
  rw [teichFam_apply, subst_smul hasSubst_verFam, subst_X hasSubst_verFam]
  cases n with
  | zero =>
    rw [verFam_zero, ← coe_substAlgHom (hasSubst_teichFam _), map_zero, smul_zero]
  | succ n =>
    rw [verFam_succ, subst_X (hasSubst_teichFam _), teichFam_apply, ← pow_mul, ← pow_succ']

omit hp in


public theorem subst_curveFam_teichFam (a : R) (n : ℕ) :
    subst (CartierModule.curveFam R) (teichFam p a n) =
      PowerSeries.rescale a (CartierModule.curveFam R n) := by
  rw [teichFam_apply, subst_smul CartierModule.hasSubst_curveFam,
    subst_X CartierModule.hasSubst_curveFam]
  cases n with
  | zero =>
    show (a ^ p ^ 0) • (PowerSeries.X : PowerSeries R) = PowerSeries.rescale a PowerSeries.X
    rw [pow_zero, pow_one, PowerSeries.rescale_X, PowerSeries.smul_eq_C_mul]
  | succ n =>
    show (a ^ p ^ (n + 1)) • (0 : PowerSeries R) = PowerSeries.rescale a 0
    rw [smul_zero, map_zero]

end MvFormalGroup

end
