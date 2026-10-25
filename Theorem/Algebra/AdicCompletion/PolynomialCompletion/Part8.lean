import Mathlib
import Def.Algebra.AdicCompletion.PolynomialCompletion.Part7
set_option autoImplicit false


namespace MvPolynomial

variable {σ : Type*} {k : Type*} [Field k]

variable [Finite σ] (q : Ideal (MvPolynomial σ k)) [hq : q.IsMaximal] (hX : ∀ i, X i ∈ q)

open IsLocalRing

theorem adicCompletionAlgEquivMvPowerSeries_of (p : MvPolynomial σ k) :
    adicCompletionAlgEquivMvPowerSeries q hX
      (AdicCompletion.of _ _ (algebraMap _ (Localization.AtPrime q) p)) = (p : MvPowerSeries σ k) :=
  adicCompletionRingEquivMvPowerSeries_of q hX p

theorem adicCompletionAlgEquivMvPowerSeries_X (i : σ) :
    adicCompletionAlgEquivMvPowerSeries q hX
      (AdicCompletion.of _ _ (algebraMap _ (Localization.AtPrime q) (X i : MvPolynomial σ k)))
        = MvPowerSeries.X i := by
  rw [adicCompletionAlgEquivMvPowerSeries_of, coe_X]

end MvPolynomial
