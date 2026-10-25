import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part5
open MeasureTheory Set StatMech StatMech.BeffaraDC


/--
[bdcLongRectangleXOffset_lt_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleXOffset_lt_period_eq
  {alpha n : ℕ}
  {k : BdcLongRectangleIndex alpha}
-- given
  (hn : 0 < n) :
-- imply
  bdcLongRectangleXOffset n k < bdcLongRectanglePeriod alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleXOffset_lt_period hn k

/--
[bdcLongRectangleYOffset_lt_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleYOffset_lt_period_eq
  {alpha n : ℕ}
  {k : BdcLongRectangleIndex alpha}
-- given
  (ha : 0 < alpha)
  (hn : 0 < n) :
-- imply
  bdcLongRectangleYOffset n k < bdcLongRectanglePeriod alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleYOffset_lt_period ha hn k

/--
[bdcLongRectangleEvent_eq_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleEvent_eq_preimage_eq
  {alpha n : ℕ}
  {k : BdcLongRectangleIndex alpha} :
-- imply
  bdcLongRectangleEvent alpha n k = translateConfig (bdcLongRectangleShift n k) ⁻¹' bdcLongRectangleBaseEvent alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleEvent_eq_preimage alpha n k

/--
[bdcLongRectangleEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleEvent_isIncreasing_eq
  {alpha n : ℕ}
  {k : BdcLongRectangleIndex alpha} :
-- imply
  IsIncreasing (bdcLongRectangleEvent alpha n k) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleEvent_isIncreasing alpha n k

/--
[bdcLongRectangleEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleEvent_measurableSet_eq
  {alpha n : ℕ}
  {k : BdcLongRectangleIndex alpha} :
-- imply
  MeasurableSet (bdcLongRectangleEvent alpha n k) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleEvent_measurableSet alpha n k

/--
[bdcLongRectangleBaseEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleBaseEvent_measurableSet_eq
  {alpha n : ℕ} :
-- imply
  MeasurableSet (bdcLongRectangleBaseEvent alpha n) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleBaseEvent_measurableSet alpha n

/--
[bdcLongRectangleEvent_probability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleEvent_probability_eq_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  {alpha n : ℕ}
  {k : BdcLongRectangleIndex alpha}
-- given
  (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu) :
-- imply
  mu.real (bdcLongRectangleEvent alpha n k) = mu.real (bdcLongRectangleBaseEvent alpha n) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleEvent_probability_eq mu hshift alpha n k

/--
[bdcLongRectangleEvent_pairwise_probability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleEvent_pairwise_probability_eq_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  {alpha n : ℕ}
  {k l : BdcLongRectangleIndex alpha}
-- given
  (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu) :
-- imply
  mu.real (bdcLongRectangleEvent alpha n k) = mu.real (bdcLongRectangleEvent alpha n l) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleEvent_pairwise_probability_eq mu hshift alpha n k l

/--
[bdcLongRectangleEvent_probability_eq_selfDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleEvent_probability_eq_selfDual_eq
  {alpha n : ℕ}
  {k : BdcLongRectangleIndex alpha} :
-- imply
  rba_selfDualMeasure.real (bdcLongRectangleEvent alpha n k) = rba_selfDualMeasure.real (bdcLongRectangleBaseEvent alpha n) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleEvent_probability_eq_selfDual alpha n k

/--
[bdcLongRectangleIndices_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleIndices_card_eq
  {alpha : ℕ} :
-- imply
  (bdcLongRectangleIndices alpha).card = 2 * alpha ^ 3 := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleIndices_card alpha

/--
[bdcLongRectangleUnion_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleUnion_isIncreasing_eq
  {alpha n : ℕ} :
-- imply
  IsIncreasing (bdcLongRectangleUnion alpha n) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleUnion_isIncreasing alpha n

/--
[bdcLongRectangleUnion_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleUnion_measurableSet_eq
  {alpha n : ℕ} :
-- imply
  MeasurableSet (bdcLongRectangleUnion alpha n) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleUnion_measurableSet alpha n

/--
[bdcLongRectangleOriginIndex_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleOriginIndex_event_eq
  {alpha n : ℕ}
-- given
  (ha : 0 < alpha) :
-- imply
  bdcLongRectangleEvent alpha n (bdcLongRectangleOriginIndex alpha ha) = bdcLongRectangleBaseEvent alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleOriginIndex_event alpha n ha

/--
[bdcLongRectangleOriginIndex_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleOriginIndex_mem_eq
  {alpha : ℕ}
-- given
  (ha : 0 < alpha) :
-- imply
  bdcLongRectangleOriginIndex alpha ha ∈ bdcLongRectangleIndices alpha := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleOriginIndex_mem alpha ha

/--
[bdcLongRectangle_polynomial_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangle_polynomial_deficit_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure mu]
  {alpha n : ℕ}
  {c epsilon : ℝ}
-- given
  (hpa : PositivelyAssociated mu)
  (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
  (ha : 0 < alpha)
  (hn : 1 ≤ n)
  (hc : 0 ≤ c)
  (hunion : 1 - mu.real (bdcLongRectangleUnion alpha n) ≤ c * (n : ℝ) ^ (-epsilon)) :
-- imply
  1 - c ^ ((1 : ℝ) / (2 * alpha ^ 3 : ℕ)) * (n : ℝ) ^ (-epsilon / (2 * alpha ^ 3 : ℕ)) ≤ mu.real (bdcLongRectangleBaseEvent alpha n) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangle_polynomial_deficit mu hpa hshift ha hn hc hunion

/--
[bdcLongRectangleUnion_deficit_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangleUnion_deficit_of_cover_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsFiniteMeasure mu]
  {alpha n : ℕ}
  {B : Set (ConfigSpace (Sym2 (Site 2)))}
  {c epsilon : ℝ}
-- given
  (hcover : B ⊆ bdcLongRectangleUnion alpha n)
  (hB : 1 - mu.real B ≤ c * (n : ℝ) ^ (-epsilon)) :
-- imply
  1 - mu.real (bdcLongRectangleUnion alpha n) ≤ c * (n : ℝ) ^ (-epsilon) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleUnion_deficit_of_cover mu B hcover hB

/--
[bdcLongRectangle_polynomial_deficit_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean)
-/
@[path]
private lemma bdcLongRectangle_polynomial_deficit_of_cover_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure mu]
  {alpha n : ℕ}
  {B : Set (ConfigSpace (Sym2 (Site 2)))}
  {c epsilon : ℝ}
-- given
  (hpa : PositivelyAssociated mu)
  (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
  (ha : 0 < alpha)
  (hn : 1 ≤ n)
  (hcover : B ⊆ bdcLongRectangleUnion alpha n)
  (hc : 0 ≤ c)
  (hB : 1 - mu.real B ≤ c * (n : ℝ) ^ (-epsilon)) :
-- imply
  1 - c ^ ((1 : ℝ) / (2 * alpha ^ 3 : ℕ)) * (n : ℝ) ^ (-epsilon / (2 * alpha ^ 3 : ℕ)) ≤ mu.real (bdcLongRectangleBaseEvent alpha n) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangle_polynomial_deficit_of_cover mu hpa hshift ha hn B hcover hc hB


-- created on 2026-10-23
