/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part10
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

theorem tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic
    {d : ℕ} (K : TailCutoff)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hadd : S.Additive)
    (hcover : ∀ c : FiniteCutoffCase d K,
      classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      S.finiteContribution c =
        keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound :=
  ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    S support tailEnvelope hzero hadd
    (externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper)
    htail htailSum


theorem tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffStableKey
    {d : ℕ} (K : TailCutoff)
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hadd : S.Additive)
    (hcover : ∀ c : FiniteCutoffCase d K,
      stableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      S.finiteContribution c =
        keyValue (classifyFiniteCutoffStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound :=
  ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    S support tailEnvelope hzero hadd
    (externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper)
    htail htailSum

end BoundedPolymerCase
end Exact3D
end StatMech
