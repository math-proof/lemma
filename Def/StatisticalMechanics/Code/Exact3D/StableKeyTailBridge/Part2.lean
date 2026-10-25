/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part10
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

noncomputable def externalStableKeyIntervalRowTable_finiteSupportCertificate_of_keyValue
    {α : Type*} [DecidableEq α] {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (classifier : α → StableKey maxDegree maxRange)
    (S : ContributionSplit α)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (support finitePrefix : Finset α)
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : α → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hcover : ∀ a, classifier a ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ a, S.finiteContribution a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    TailSummability.FiniteSupportCertificate α :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
      rows fallback classifier S.finiteContribution keyValue
      hcover hvalue hrow hrowUpper)
    htail htailSum


noncomputable def externalStableKeyIntervalRowTable_finiteSupportCertificate_of_exactKeySet
    {α : Type*} [DecidableEq α] {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey maxDegree maxRange))
    (classifier : α → StableKey maxDegree maxRange)
    (S : ContributionSplit α)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (support finitePrefix : Finset α)
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : α → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ a, classifier a ∈ expected)
    (hvalue : ∀ a, S.finiteContribution a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    TailSummability.FiniteSupportCertificate α :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (externalStableKeyIntervalRowTable_finiteTableUpperBound_of_exactKeySet
      rows fallback expected classifier S.finiteContribution keyValue hexact
      hcover hvalue hrow hrowUpper)
    htail htailSum


noncomputable def finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
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
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper)
    htail htailSum


noncomputable def
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic_exactKeySet
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey K.maxDegree K.maxRange))
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ c : FiniteCutoffCase d K,
      classifyByMinimalCubicStableKey c ∈ expected)
    (hvalue : ∀ c,
      S.finiteContribution c =
        keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  externalStableKeyIntervalRowTable_finiteSupportCertificate_of_exactKeySet
    rows fallback expected (classifyFiniteCutoffMinimalCubicStableKey K) S
    keyValue support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    hexact (fun c => hcover (classifyFiniteCutoffCoordinate K c)) hvalue
    hrow hrowUpper htail htailSum


noncomputable def finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffStableKey
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
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
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd
    (externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue
      K rows fallback S.finiteContribution keyValue hcover hvalue hrow hrowUpper)
    htail htailSum


noncomputable def
    finiteSupportCertificate_of_externalStableKeyIntervalRows_finiteCutoffStableKey_exactKeySet
    {d : ℕ} (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (S : ContributionSplit (FiniteCutoffCoordinate d K))
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey K.maxDegree K.maxRange))
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    (support finitePrefix : Finset (FiniteCutoffCoordinate d K))
    {finiteBound tailEnvelopeBound : ℝ}
    (tailEnvelope : FiniteCutoffCoordinate d K → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ c : FiniteCutoffCase d K, stableKey c ∈ expected)
    (hvalue : ∀ c,
      S.finiteContribution c =
        keyValue (classifyFiniteCutoffStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    TailSummability.FiniteSupportCertificate (FiniteCutoffCoordinate d K) :=
  externalStableKeyIntervalRowTable_finiteSupportCertificate_of_exactKeySet
    rows fallback expected (classifyFiniteCutoffStableKey K) S keyValue
    support finitePrefix tailEnvelope hprefix hzero hnonneg hadd hexact
    (fun c => hcover (classifyFiniteCutoffCoordinate K c)) hvalue hrow
    hrowUpper htail htailSum


end BoundedPolymerCase
end Exact3D
end StatMech
