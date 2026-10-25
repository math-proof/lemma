import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexBetheLogObservable_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLogReduction.lean)
-/
@[path]
private lemma sixVertexBetheLogObservable_neg_eq
  {c p : Real} :
-- imply
  sixVertexBetheLogObservable c (-p) = sixVertexBetheLogObservable c p := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheLogObservable_neg c p

/--
[sum_sixVertexBetheLogObservable_evenSymmetricLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLogReduction.lean)
-/
@[path]
private lemma sum_sixVertexBetheLogObservable_evenSymmetricLift_eq
  {c : Real}
  {m : Nat}
-- given
  (q : Fin m -> Real) :
-- imply
  (∑ i : Fin (m + m), sixVertexBetheLogObservable c (sixVertexEvenSymmetricLift m q i)) = 2 * ∑ j : Fin m, sixVertexBetheLogObservable c (q j) := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBetheLogObservable_evenSymmetricLift c m q

/--
[sixVertexCanonicalDensityPerronEmpiricalLogObservable_eq_rootAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLogReduction.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronEmpiricalLogObservable_eq_rootAverage_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexBetheLogObservable c) k = sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronEmpiricalLogObservable_eq_rootAverage hc k

/--
[sixVertexCentralWidthRate_eventuallyEq_canonicalDensityEmpiricalLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLogReduction.lean)
-/
@[path]
private lemma sixVertexCentralWidthRate_eventuallyEq_canonicalDensityEmpiricalLog_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCentralWidthRate c =ᶠ[atTop] fun k => Real.log 2 / (sixVertexFourWidth 0 k : Real) + sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexBetheLogObservable c) k := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralWidthRate_eventuallyEq_canonicalDensityEmpiricalLog hc

/--
[sixVertexCentralWidthRate_tendsto_iff_canonicalDensityEmpiricalLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLogReduction.lean)
-/
@[path]
private lemma sixVertexCentralWidthRate_tendsto_iff_canonicalDensityEmpiricalLog_eq
  {c a : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) ↔ Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexBetheLogObservable c)) atTop (nhds a) := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralWidthRate_tendsto_iff_canonicalDensityEmpiricalLog hc


-- created on 2026-10-23
