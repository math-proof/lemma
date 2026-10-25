-- Carved from Lemma/Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean: instance decls only.
import Mathlib
import Instance.AlgebraicCurve_RatFuncPlaces
import Lemma.AlgebraicCurve.RatFuncPlaceInfty

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

instance instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions :
    Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

end PlaceInfty

variable {K}

variable (K)

end RationalFunctionField

end AlgebraicCurve
end
