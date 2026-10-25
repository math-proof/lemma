import Lemma.WeierstrassCurve.Velu
import Def.WeierstrassCurve_VeluQuotientOfSums

set_option autoImplicit false

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


@[simp] lemma veluQuotientOfSums_a₁ (t w : R) : (W.veluQuotientOfSums t w).a₁ = W.a₁ := rfl
@[simp] lemma veluQuotientOfSums_a₂ (t w : R) : (W.veluQuotientOfSums t w).a₂ = W.a₂ := rfl
@[simp] lemma veluQuotientOfSums_a₃ (t w : R) : (W.veluQuotientOfSums t w).a₃ = W.a₃ := rfl
lemma veluQuotientOfSums_a₄ (t w : R) : (W.veluQuotientOfSums t w).a₄ = W.a₄ - 5 * t := rfl
lemma veluQuotientOfSums_a₆ (t w : R) :
    (W.veluQuotientOfSums t w).a₆ = W.a₆ - W.b₂ * t - 7 * w := rfl

theorem veluQuotient_eq_veluQuotientOfSums (S : Finset (R × R)) :
    W.veluQuotient S = W.veluQuotientOfSums (W.veluTSum S) (W.veluWSum S) := rfl

theorem veluQuotient_eq_veluQuotientOfSums_of_sums {S : Finset (R × R)} {t w : R}
    (ht : W.veluTSum S = t) (hw : W.veluWSum S = w) :
    W.veluQuotient S = W.veluQuotientOfSums t w := by
  subst ht hw; rfl

end WeierstrassCurve
