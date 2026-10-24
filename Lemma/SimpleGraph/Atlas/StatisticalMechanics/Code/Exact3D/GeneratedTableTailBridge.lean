import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.BoundedPolymerCase


/--
[generatedIntervalTable_finiteTableUpperBound_finiteCutoff_of_caseValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridge.lean)
-/
@[path]
private lemma generatedIntervalTable_finiteTableUpperBound_finiteCutoff_of_caseValue_eq
  {d : ℕ}
  {K : TailCutoff}
  {intervalOf : FiniteCutoffCase d K → RatInterval}
  {value : FiniteCutoffCoordinate d K → ℝ}
  {caseValue : FiniteCutoffCase d K → ℝ}
  {finiteBound : ℝ}
-- given
  (hvalue : ∀ c, value c = caseValue (classifyFiniteCutoffCoordinate K c))
  (hcase : ∀ c, (intervalOf c).MemR (caseValue c))
  (hupper : ∀ c, c ∈ (generatedIntervalTable intervalOf).cases → ((intervalOf c).upper : ℝ) ≤ finiteBound) :
-- imply
  FiniteTableUpperBound (generatedIntervalTable intervalOf) (classifyFiniteCutoffCoordinate K) value finiteBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedIntervalTable_finiteTableUpperBound_finiteCutoff_of_caseValue K intervalOf value caseValue hvalue hcase hupper

/--
[generatedCubicIntervalTable_finiteTableUpperBound_finiteCutoff_of_classValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridge.lean)
-/
@[path]
private lemma generatedCubicIntervalTable_finiteTableUpperBound_finiteCutoff_of_classValue_eq
  {d : ℕ}
  {K : TailCutoff}
  {intervalOf : CubicClass d K.radius K.maxDegree K.maxRange → RatInterval}
  {value : FiniteCutoffCoordinate d K → ℝ}
  {classValue : CubicClass d K.radius K.maxDegree K.maxRange → ℝ}
  {finiteBound : ℝ}
-- given
  (hvalue : ∀ c, value c = classValue (classifyFiniteCutoffCubicClass K c))
  (hclass : ∀ q, (intervalOf q).MemR (classValue q))
  (hupper : ∀ q, q ∈ (generatedCubicIntervalTable intervalOf).cases → ((intervalOf q).upper : ℝ) ≤ finiteBound) :
-- imply
  FiniteTableUpperBound (generatedCubicIntervalTable intervalOf) (classifyFiniteCutoffCubicClass K) value finiteBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedCubicIntervalTable_finiteTableUpperBound_finiteCutoff_of_classValue K intervalOf value classValue hvalue hclass hupper

/--
[generatedStableKeyIntervalTable_finiteTableUpperBound_finiteCutoff_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridge.lean)
-/
@[path]
private lemma generatedStableKeyIntervalTable_finiteTableUpperBound_finiteCutoff_of_keyValue_eq
  {d : ℕ}
  {K : TailCutoff}
  {intervalOf : StableKey K.maxDegree K.maxRange → RatInterval}
  {value : FiniteCutoffCoordinate d K → ℝ}
  {keyValue : StableKey K.maxDegree K.maxRange → ℝ}
  {finiteBound : ℝ}
-- given
  (hvalue : ∀ c, value c = keyValue (classifyFiniteCutoffStableKey K c))
  (hkey : ∀ k, k ∈ (generatedStableKeyIntervalTable (d := d) (R := K.radius) intervalOf).cases → (intervalOf k).MemR (keyValue k))
  (hupper : ∀ k, k ∈ (generatedStableKeyIntervalTable (d := d) (R := K.radius) intervalOf).cases → ((intervalOf k).upper : ℝ) ≤ finiteBound) :
-- imply
  FiniteTableUpperBound (generatedStableKeyIntervalTable (d := d) (R := K.radius) intervalOf) (classifyFiniteCutoffStableKey K) value finiteBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedStableKeyIntervalTable_finiteTableUpperBound_finiteCutoff_of_keyValue K intervalOf value keyValue hvalue hkey hupper

/--
[generatedMinimalCubicStableKeyTable_finiteTableUpperBound_finiteCutoff_of_keyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridge.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyTable_finiteTableUpperBound_finiteCutoff_of_keyValue_eq
  {d : ℕ}
  {K : TailCutoff}
  {intervalOf : StableKey K.maxDegree K.maxRange → RatInterval}
  {value : FiniteCutoffCoordinate d K → ℝ}
  {keyValue : StableKey K.maxDegree K.maxRange → ℝ}
  {finiteBound : ℝ}
-- given
  (hvalue : ∀ c, value c = keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
  (hkey : ∀ k, k ∈ (generatedMinimalCubicStableKeyTable (d := d) (R := K.radius) intervalOf).cases → (intervalOf k).MemR (keyValue k))
  (hupper : ∀ k, k ∈ (generatedMinimalCubicStableKeyTable (d := d) (R := K.radius) intervalOf).cases → ((intervalOf k).upper : ℝ) ≤ finiteBound) :
-- imply
  FiniteTableUpperBound (generatedMinimalCubicStableKeyTable (d := d) (R := K.radius) intervalOf) (classifyFiniteCutoffMinimalCubicStableKey K) value finiteBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.generatedMinimalCubicStableKeyTable_finiteTableUpperBound_finiteCutoff_of_keyValue K intervalOf value keyValue hvalue hkey hupper

/--
[tsum_total_le_of_generatedStableKeyIntervalTable_finiteCutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridge.lean)
-/
@[path]
private lemma tsum_total_le_of_generatedStableKeyIntervalTable_finiteCutoff_eq
  {d : ℕ}
  {K : TailCutoff}
  {S : ContributionSplit (FiniteCutoffCoordinate d K)}
  {intervalOf : StableKey K.maxDegree K.maxRange → RatInterval}
  {keyValue : StableKey K.maxDegree K.maxRange → ℝ}
  {support : Finset (FiniteCutoffCoordinate d K)}
  {finiteBound tailBound : ℝ}
  {tailEnvelope : FiniteCutoffCoordinate d K → ℝ}
-- given
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
  (hadd : S.Additive)
  (hvalue : ∀ c, S.finiteContribution c = keyValue (classifyFiniteCutoffStableKey K c))
  (hkey : ∀ k, k ∈ (generatedStableKeyIntervalTable (d := d) (R := K.radius) intervalOf).cases → (intervalOf k).MemR (keyValue k))
  (hupper : ∀ k, k ∈ (generatedStableKeyIntervalTable (d := d) (R := K.radius) intervalOf).cases → ((intervalOf k).upper : ℝ) ≤ finiteBound)
  (htail : S.TailEnvelopeOn support tailEnvelope)
  (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (support.card : ℝ) * finiteBound + tailBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.tsum_total_le_of_generatedStableKeyIntervalTable_finiteCutoff K S intervalOf keyValue support tailEnvelope hzero hadd hvalue hkey hupper htail htailSum

/--
[tsum_total_le_of_generatedMinimalCubicStableKeyTable_finiteCutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridge.lean)
-/
@[path]
private lemma tsum_total_le_of_generatedMinimalCubicStableKeyTable_finiteCutoff_eq
  {d : ℕ}
  {K : TailCutoff}
  {S : ContributionSplit (FiniteCutoffCoordinate d K)}
  {intervalOf : StableKey K.maxDegree K.maxRange → RatInterval}
  {keyValue : StableKey K.maxDegree K.maxRange → ℝ}
  {support : Finset (FiniteCutoffCoordinate d K)}
  {finiteBound tailBound : ℝ}
  {tailEnvelope : FiniteCutoffCoordinate d K → ℝ}
-- given
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
  (hadd : S.Additive)
  (hvalue : ∀ c, S.finiteContribution c = keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
  (hkey : ∀ k, k ∈ (generatedMinimalCubicStableKeyTable (d := d) (R := K.radius) intervalOf).cases → (intervalOf k).MemR (keyValue k))
  (hupper : ∀ k, k ∈ (generatedMinimalCubicStableKeyTable (d := d) (R := K.radius) intervalOf).cases → ((intervalOf k).upper : ℝ) ≤ finiteBound)
  (htail : S.TailEnvelopeOn support tailEnvelope)
  (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (support.card : ℝ) * finiteBound + tailBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.tsum_total_le_of_generatedMinimalCubicStableKeyTable_finiteCutoff K S intervalOf keyValue support tailEnvelope hzero hadd hvalue hkey hupper htail htailSum

/--
[tsum_total_le_of_generatedIntervalTable_finiteCutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridge.lean)
-/
@[path]
private lemma tsum_total_le_of_generatedIntervalTable_finiteCutoff_eq
  {d : ℕ}
  {K : TailCutoff}
  {S : ContributionSplit (FiniteCutoffCoordinate d K)}
  {intervalOf : FiniteCutoffCase d K → RatInterval}
  {caseValue : FiniteCutoffCase d K → ℝ}
  {support : Finset (FiniteCutoffCoordinate d K)}
  {finiteBound tailBound : ℝ}
  {tailEnvelope : FiniteCutoffCoordinate d K → ℝ}
-- given
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
  (hadd : S.Additive)
  (hvalue : ∀ c, S.finiteContribution c = caseValue (classifyFiniteCutoffCoordinate K c))
  (hcase : ∀ c, (intervalOf c).MemR (caseValue c))
  (hupper : ∀ c, c ∈ (generatedIntervalTable intervalOf).cases → ((intervalOf c).upper : ℝ) ≤ finiteBound)
  (htail : S.TailEnvelopeOn support tailEnvelope)
  (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (support.card : ℝ) * finiteBound + tailBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.tsum_total_le_of_generatedIntervalTable_finiteCutoff K S intervalOf caseValue support tailEnvelope hzero hadd hvalue hcase hupper htail htailSum

/--
[tsum_total_le_of_generatedCubicIntervalTable_finiteCutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridge.lean)
-/
@[path]
private lemma tsum_total_le_of_generatedCubicIntervalTable_finiteCutoff_eq
  {d : ℕ}
  {K : TailCutoff}
  {S : ContributionSplit (FiniteCutoffCoordinate d K)}
  {intervalOf : CubicClass d K.radius K.maxDegree K.maxRange → RatInterval}
  {classValue : CubicClass d K.radius K.maxDegree K.maxRange → ℝ}
  {support : Finset (FiniteCutoffCoordinate d K)}
  {finiteBound tailBound : ℝ}
  {tailEnvelope : FiniteCutoffCoordinate d K → ℝ}
-- given
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
  (hadd : S.Additive)
  (hvalue : ∀ c, S.finiteContribution c = classValue (classifyFiniteCutoffCubicClass K c))
  (hclass : ∀ q, (intervalOf q).MemR (classValue q))
  (hupper : ∀ q, q ∈ (generatedCubicIntervalTable intervalOf).cases → ((intervalOf q).upper : ℝ) ≤ finiteBound)
  (htail : S.TailEnvelopeOn support tailEnvelope)
  (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (support.card : ℝ) * finiteBound + tailBound := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.tsum_total_le_of_generatedCubicIntervalTable_finiteCutoff K S intervalOf classValue support tailEnvelope hzero hadd hvalue hclass hupper htail htailSum


-- created on 2026-10-23
