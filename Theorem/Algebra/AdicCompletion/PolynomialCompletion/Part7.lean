import Mathlib
import Def.Algebra.AdicCompletion.PolynomialCompletion.Part6
set_option autoImplicit false


namespace MvPolynomial

variable {σ : Type*} {k : Type*} [Field k]

variable [Finite σ] (q : Ideal (MvPolynomial σ k)) [hq : q.IsMaximal] (hX : ∀ i, X i ∈ q)

open IsLocalRing

theorem adicCompletionRingEquivMvPowerSeries_of (p : MvPolynomial σ k) :
    adicCompletionRingEquivMvPowerSeries q hX
      (AdicCompletion.of _ _ (algebraMap _ (Localization.AtPrime q) p)) = (p : MvPowerSeries σ k) := by
  have h := eq_idealOfVars_of_X_mem q hX
  subst h
  simp only [adicCompletionRingEquivMvPowerSeries, RingEquiv.trans_apply]
  rw [← AdicCompletion.localizationEquiv_of, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq,
    AlgEquiv.coe_ringEquiv, MvPowerSeries.toAdicCompletionAlgEquiv_apply,
    MvPowerSeries.toAdicCompletion_coe]

end MvPolynomial
