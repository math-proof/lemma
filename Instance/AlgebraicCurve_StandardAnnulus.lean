-- Carved from Lemma/Definitions/Def_AlgebraicCurve_StandardAnnulus.lean: instance decls only.
import Lemma.ModularCurve.FinitePlaceLift
import Instance.AlgebraicCurve_RatFuncPlaces
import Lemma.AlgebraicCurve.RatFuncPlaceInfty
import Lemma.AlgebraicCurve.SemistableCharts
import Lemma.AlgebraicCurve.StandardAnnulus

namespace AlgebraicCurve.GaussReduction

open Polynomial

variable {K : Type*} [Field K] (A : ValuationSubring K)

instance isLocalHom_constToGauss : IsLocalHom (constToGauss A) := by
  constructor
  intro a ha
  by_contra hnu
  have hlt : A.valuation (a : K) < 1 := by
    rcases lt_or_eq_of_le (A.valuation_le_one a) with h | h
    · exact h
    · exact absurd ((A.valuation_eq_one_iff a).mpr h) hnu
  have : gaussValuation A ((constToGauss A a : ↥(gaussIntegers A)) : RatFunc K) < 1 := by
    rw [constToGauss_coe, gaussValuation_algebraMap_const]
    exact hlt
  exact (not_isUnit_gauss_iff A _).mpr this ha


end AlgebraicCurve.GaussReduction


