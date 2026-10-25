-- Carved from Lemma/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean: instance decls only.
import Mathlib
import Instance.AlgebraicCurve_DivisorClassGroup
import Lemma.AlgebraicCurve.RatFuncPlaces

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing

open scoped Polynomial

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

instance : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

instance : v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one.mp (v.algebraMap_mem' a)


end Place


end AlgebraicCurve

end
