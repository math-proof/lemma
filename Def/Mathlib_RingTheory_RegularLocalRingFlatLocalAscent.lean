import Mathlib
import Lemma.Ideal.RegularLocalRingQuotientRegular
import Theorems.Thm_IsRegularLocalRing_isDomain
import Lemma.Ideal.RegularLocalRingRegularSequenceAscent

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open IsLocalRing RingTheory
open scoped Pointwise

namespace RegularFlatLocalAscent

universe u v

def quotSpanSingletonEquivQuotSMulTop {R : Type u} [CommRing R] (x : R) :
    (R ⧸ Ideal.span {x}) ≃ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x R :=
  (Submodule.quotEquivOfEq (Ideal.span {x}) (x • (⊤ : Submodule R R))
    (by rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul,
      Ideal.mul_top])).extendScalarsOfSurjective Ideal.Quotient.mk_surjective


end RegularFlatLocalAscent

end
