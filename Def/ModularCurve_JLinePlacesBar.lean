import Mathlib
import Lemma.ModularCurve.ArithmeticGalois
import Lemma.AlgebraicCurve.RatFuncPlaces
import Lemma.AlgebraicCurve.RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Instance.ModularCurve_JLinePlacesBar
import Abbrev.ModularCurve_JLinePlacesBar

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace ModularCurve

set_option synthInstance.maxHeartbeats 400000

variable (N : ℕ) [NeZero N]

theorem transcendental_jLineBar_gen :
    Transcendental (AlgebraicClosure ℚ)
      (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        ↥(modularFunctionFieldBar N)) :=
  transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N

def jLineBarRingEquiv : RatFunc (AlgebraicClosure ℚ) ≃+* ↥(jLineBar N) :=
  RingEquiv.ofBijective
    (RatFunc.algEquivOfTranscendental _ (transcendental_jLineBar_gen N))
    (EquivLike.bijective _)

theorem jLineBarRingEquiv_apply (f : RatFunc (AlgebraicClosure ℚ)) :
    jLineBarRingEquiv N f = RatFunc.algEquivOfTranscendental _ (transcendental_jLineBar_gen N) f := rfl

theorem jLineBarRingEquiv_algebraMap (a : AlgebraicClosure ℚ) :
    jLineBarRingEquiv N (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) a) = algebraMap (AlgebraicClosure ℚ) ↥(jLineBar N) a :=
  (RatFunc.algEquivOfTranscendental _ (transcendental_jLineBar_gen N)).commutes a

theorem jLineBarRingEquiv_X :
    (jLineBarRingEquiv N RatFunc.X : ↥(modularFunctionFieldBar N))
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :=
  RatFunc.algEquivOfTranscendental_X _ (transcendental_jLineBar_gen N)

@[reducible] def instDecidableEqRatFuncAlgebraicClosure : DecidableEq (RatFunc (AlgebraicClosure ℚ)) := Classical.decEq _

attribute [local instance] instDecidableEqRatFuncAlgebraicClosure

def jLineBarPlace1728 : Place (AlgebraicClosure ℚ) ↥(jLineBar N) :=
  Place.congrRingEquiv (jLineBarRingEquiv N) (jLineBarRingEquiv_algebraMap N) (placeOfPoint (AlgebraicClosure ℚ) 1728)

def jLineBarPlaceZero : Place (AlgebraicClosure ℚ) ↥(jLineBar N) :=
  Place.congrRingEquiv (jLineBarRingEquiv N) (jLineBarRingEquiv_algebraMap N) (placeOfPoint (AlgebraicClosure ℚ) 0)

def jLineBarPlaceInfty : Place (AlgebraicClosure ℚ) ↥(jLineBar N) :=
  Place.congrRingEquiv (jLineBarRingEquiv N) (jLineBarRingEquiv_algebraMap N) (placeInfty (AlgebraicClosure ℚ))

end ModularCurve

end
