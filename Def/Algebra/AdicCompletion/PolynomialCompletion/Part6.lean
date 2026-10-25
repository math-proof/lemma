import Mathlib
import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part6
set_option autoImplicit false


namespace MvPolynomial

variable {σ : Type*} {k : Type*} [Field k]

variable [Finite σ] (q : Ideal (MvPolynomial σ k)) [hq : q.IsMaximal] (hX : ∀ i, X i ∈ q)

open IsLocalRing

noncomputable def adicCompletionRingEquivMvPowerSeries :
    AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
      ≃+* MvPowerSeries σ k := by
  have h := eq_idealOfVars_of_X_mem q hX
  subst h
  exact (AdicCompletion.localizationEquiv (idealOfVars σ k)).symm.trans
    (MvPowerSeries.toAdicCompletionAlgEquiv σ k).toRingEquiv.symm

end MvPolynomial
