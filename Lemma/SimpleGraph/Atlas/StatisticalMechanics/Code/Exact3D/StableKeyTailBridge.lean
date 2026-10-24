import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.BoundedPolymerCase


/--
[intervalOfRows_upper_le_of_mem_keyFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean)
-/
@[path]
private lemma intervalOfRows_upper_le_of_mem_keyFinset_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {bound : ℝ}
  {k : StableKey maxDegree maxRange}
-- given
  (hrowUpper : ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ bound)
  (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
-- imply
  (((intervalOfRows rows fallback k).upper : ℚ) : ℝ) ≤ bound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.intervalOfRows_upper_le_of_mem_keyFinset rows fallback hrowUpper hk

/--
[externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean)
-/
@[path]
private lemma externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {classifier : α → StableKey maxDegree maxRange}
  {value : α → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
  {finiteBound : ℝ}
-- given
  (hcover : ∀ a, classifier a ∈ stableKeyIntervalRowKeyFinset rows)
  (hvalue : ∀ a, value a = keyValue (classifier a))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey))
  (hrowUpper : ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
-- imply
  FiniteTableUpperBound (externalStableKeyIntervalRowTable rows fallback) classifier value finiteBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue rows fallback classifier value keyValue hcover hvalue hrow hrowUpper

/--
[externalStableKeyIntervalRowTable_finiteTableUpperBound_of_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean)
-/
@[path]
private lemma externalStableKeyIntervalRowTable_finiteTableUpperBound_of_exactKeySet_eq
  {maxDegree maxRange : ℕ}
  {rows : List (StableKeyIntervalRow maxDegree maxRange)}
  {fallback : RatInterval}
  {expected : Finset (StableKey maxDegree maxRange)}
  {classifier : α → StableKey maxDegree maxRange}
  {value : α → ℝ}
  {keyValue : StableKey maxDegree maxRange → ℝ}
  {finiteBound : ℝ}
-- given
  (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
  (hcover : ∀ a, classifier a ∈ expected)
  (hvalue : ∀ a, value a = keyValue (classifier a))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey))
  (hrowUpper : ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
-- imply
  FiniteTableUpperBound (externalStableKeyIntervalRowTable rows fallback) classifier value finiteBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRowTable_finiteTableUpperBound_of_exactKeySet rows fallback expected classifier value keyValue hexact hcover hvalue hrow hrowUpper

/--
[externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean)
-/
@[path]
private lemma externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue_eq
  {d : ℕ}
  {K : TailCutoff}
  {rows : List (StableKeyIntervalRow K.maxDegree K.maxRange)}
  {fallback : RatInterval}
  {value : FiniteCutoffCoordinate d K → ℝ}
  {keyValue : StableKey K.maxDegree K.maxRange → ℝ}
  {finiteBound : ℝ}
-- given
  (hcover : ∀ c : FiniteCutoffCase d K, classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset rows)
  (hvalue : ∀ c, value c = keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey))
  (hrowUpper : ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
-- imply
  FiniteTableUpperBound (externalStableKeyIntervalRowTable rows fallback) (classifyFiniteCutoffMinimalCubicStableKey K) value finiteBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue K rows fallback value keyValue hcover hvalue hrow hrowUpper

/--
[externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean)
-/
@[path]
private lemma externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue_eq
  {d : ℕ}
  {K : TailCutoff}
  {rows : List (StableKeyIntervalRow K.maxDegree K.maxRange)}
  {fallback : RatInterval}
  {value : FiniteCutoffCoordinate d K → ℝ}
  {keyValue : StableKey K.maxDegree K.maxRange → ℝ}
  {finiteBound : ℝ}
-- given
  (hcover : ∀ c : FiniteCutoffCase d K, stableKey c ∈ stableKeyIntervalRowKeyFinset rows)
  (hvalue : ∀ c, value c = keyValue (classifyFiniteCutoffStableKey K c))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey))
  (hrowUpper : ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
-- imply
  FiniteTableUpperBound (externalStableKeyIntervalRowTable rows fallback) (classifyFiniteCutoffStableKey K) value finiteBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue K rows fallback value keyValue hcover hvalue hrow hrowUpper

/--
[tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean)
-/
@[path]
private lemma tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic_eq
  {d : ℕ}
  {K : TailCutoff}
  {S : ContributionSplit (FiniteCutoffCoordinate d K)}
  {rows : List (StableKeyIntervalRow K.maxDegree K.maxRange)}
  {fallback : RatInterval}
  {keyValue : StableKey K.maxDegree K.maxRange → ℝ}
  {support : Finset (FiniteCutoffCoordinate d K)}
  {finiteBound tailBound : ℝ}
  {tailEnvelope : FiniteCutoffCoordinate d K → ℝ}
-- given
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
  (hadd : S.Additive)
  (hcover : ∀ c : FiniteCutoffCase d K, classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset rows)
  (hvalue : ∀ c, S.finiteContribution c = keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey))
  (hrowUpper : ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
  (htail : S.TailEnvelopeOn support tailEnvelope)
  (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (support.card : ℝ) * finiteBound + tailBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic K S rows fallback keyValue support tailEnvelope hzero hadd hcover hvalue hrow hrowUpper htail htailSum

/--
[tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffStableKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean)
-/
@[path]
private lemma tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffStableKey_eq
  {d : ℕ}
  {K : TailCutoff}
  {S : ContributionSplit (FiniteCutoffCoordinate d K)}
  {rows : List (StableKeyIntervalRow K.maxDegree K.maxRange)}
  {fallback : RatInterval}
  {keyValue : StableKey K.maxDegree K.maxRange → ℝ}
  {support : Finset (FiniteCutoffCoordinate d K)}
  {finiteBound tailBound : ℝ}
  {tailEnvelope : FiniteCutoffCoordinate d K → ℝ}
-- given
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
  (hadd : S.Additive)
  (hcover : ∀ c : FiniteCutoffCase d K, stableKey c ∈ stableKeyIntervalRowKeyFinset rows)
  (hvalue : ∀ c, S.finiteContribution c = keyValue (classifyFiniteCutoffStableKey K c))
  (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey))
  (hrowUpper : ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
  (htail : S.TailEnvelopeOn support tailEnvelope)
  (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (support.card : ℝ) * finiteBound + tailBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffStableKey K S rows fallback keyValue support tailEnvelope hzero hadd hcover hvalue hrow hrowUpper htail htailSum


-- created on 2026-10-23
