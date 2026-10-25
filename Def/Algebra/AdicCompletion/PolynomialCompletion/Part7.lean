import Mathlib
import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part7
set_option autoImplicit false


namespace MvPolynomial

variable {σ : Type*} {k : Type*} [Field k]

variable [Finite σ] (q : Ideal (MvPolynomial σ k)) [hq : q.IsMaximal] (hX : ∀ i, X i ∈ q)

open IsLocalRing

noncomputable def adicCompletionAlgEquivMvPowerSeries :
    AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
      ≃ₐ[k] MvPowerSeries σ k :=
  AlgEquiv.ofRingEquiv (f := adicCompletionRingEquivMvPowerSeries q hX) fun x => by
    rw [AdicCompletion.algebraMap_apply, IsScalarTower.algebraMap_apply k (MvPolynomial σ k)
      (Localization.AtPrime q), adicCompletionRingEquivMvPowerSeries_of, algebraMap_eq, coe_C]
    rfl

end MvPolynomial
