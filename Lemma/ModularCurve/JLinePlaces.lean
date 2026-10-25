import Mathlib
import Def.ModularCurve_RouteBCoordRing
import Lemma.AlgebraicCurve.RatFuncPlaces
import Lemma.AlgebraicCurve.RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_transcendental_jq
import Instance.ModularCurve_JLinePlaces

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace ModularCurve

section Tower

variable (N : ℕ) [NeZero N]

@[reducible] def jAdjoinAlgebra : Algebra ℚ⟮jq⟯ (modularFunctionField N) :=
  (jAdjoinRingHom N).toAlgebra

attribute [local instance] jAdjoinAlgebra

theorem algebraMap_jGen_val : (algebraMap ℚ⟮jq⟯ (modularFunctionField N) jGen : LaurentSeries ℚ) = jq :=
  rfl

end Tower

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

def jLineRingEquiv : RatFunc ℚ ≃+* ℚ⟮jq⟯ :=
  RingEquiv.ofBijective (RatFunc.algEquivOfTranscendental jq transcendental_jq)
    (EquivLike.bijective _)

theorem jLineRingEquiv_apply (f : RatFunc ℚ) :
    jLineRingEquiv f = RatFunc.algEquivOfTranscendental jq transcendental_jq f := rfl

theorem jLineRingEquiv_X : jLineRingEquiv RatFunc.X = jGen :=
  Subtype.ext (RatFunc.algEquivOfTranscendental_X jq transcendental_jq)

@[reducible] def instDecidableEqRatFuncRat : DecidableEq (RatFunc ℚ) := Classical.decEq _

attribute [local instance] instDecidableEqRatFuncRat

def jLinePlace1728 : Place ℚ ℚ⟮jq⟯ :=
  Place.congrRingEquiv jLineRingEquiv (RingHom.map_rat_algebraMap jLineRingEquiv.toRingHom)
    (placeOfPoint ℚ 1728)

def jLinePlaceZero : Place ℚ ℚ⟮jq⟯ :=
  Place.congrRingEquiv jLineRingEquiv (RingHom.map_rat_algebraMap jLineRingEquiv.toRingHom)
    (placeOfPoint ℚ 0)

def jLinePlaceInfty : Place ℚ ℚ⟮jq⟯ :=
  Place.congrRingEquiv jLineRingEquiv (RingHom.map_rat_algebraMap jLineRingEquiv.toRingHom)
    (placeInfty ℚ)

end ModularCurve

end
