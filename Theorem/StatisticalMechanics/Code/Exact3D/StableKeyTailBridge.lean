/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part10
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

theorem intervalOfRows_upper_le_of_mem_keyFinset {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) {bound : ℝ}
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ bound)
    {k : StableKey maxDegree maxRange}
    (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
    (((intervalOfRows rows fallback k).upper : ℚ) : ℝ) ≤ bound := by
  classical
  have hex : ∃ row, row ∈ rows ∧ row.key.toKey = k := by
    simpa [stableKeyIntervalRowKeyFinset, stableKeyIntervalRowRecords,
      validRecordKeyFinset, validRecordKeyList] using hk
  rw [intervalOfRows, dif_pos hex]
  exact hrowUpper (Classical.choose hex) (Classical.choose_spec hex).1


theorem externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
    {α : Type*} {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    {finiteBound : ℝ}
    (hcover : ∀ a, classifier a ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound (externalStableKeyIntervalRowTable rows fallback)
      classifier value finiteBound := by
  classical
  have hcovsound :=
    externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
      rows fallback classifier value keyValue hcover hvalue hrow
  refine ⟨hcovsound.1, hcovsound.2, ?_⟩
  intro k hk
  simpa [externalStableKeyIntervalRowTable, externalStableKeyIntervalTable] using
    intervalOfRows_upper_le_of_mem_keyFinset rows fallback hrowUpper
      (by
        simpa [externalStableKeyIntervalRowTable, externalStableKeyIntervalTable,
          stableKeyIntervalRowKeyFinset] using hk)


theorem externalStableKeyIntervalRowTable_finiteTableUpperBound_of_exactKeySet
    {α : Type*} {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey maxDegree maxRange))
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    {finiteBound : ℝ}
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ a, classifier a ∈ expected)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound (externalStableKeyIntervalRowTable rows fallback)
      classifier value finiteBound :=
  externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
    rows fallback classifier value keyValue
    (StableKeyIntervalRow.classifier_mem_rows_of_exactKeySet
      hexact classifier hcover)
    hvalue hrow hrowUpper


theorem externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffMinimalCubic_of_keyValue
    {d : ℕ} (K : TailCutoff)
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (value : FiniteCutoffCoordinate d K → ℝ)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    {finiteBound : ℝ}
    (hcover : ∀ c : FiniteCutoffCase d K,
      classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      value c =
        keyValue (classifyFiniteCutoffMinimalCubicStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound
      (externalStableKeyIntervalRowTable rows fallback)
      (classifyFiniteCutoffMinimalCubicStableKey K) value finiteBound :=
  externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
    rows fallback (classifyFiniteCutoffMinimalCubicStableKey K) value keyValue
    (fun c => hcover (classifyFiniteCutoffCoordinate K c))
    hvalue hrow hrowUpper


theorem externalStableKeyIntervalRows_finiteTableUpperBound_finiteCutoffStableKey_of_keyValue
    {d : ℕ} (K : TailCutoff)
    (rows : List (StableKeyIntervalRow K.maxDegree K.maxRange))
    (fallback : RatInterval)
    (value : FiniteCutoffCoordinate d K → ℝ)
    (keyValue : StableKey K.maxDegree K.maxRange → ℝ)
    {finiteBound : ℝ}
    (hcover : ∀ c : FiniteCutoffCase d K,
      stableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      value c =
        keyValue (classifyFiniteCutoffStableKey K c))
    (hrow : ∀ row, row ∈ rows →
      row.interval.MemR (keyValue row.key.toKey))
    (hrowUpper :
      ∀ row, row ∈ rows → ((row.interval.upper : ℚ) : ℝ) ≤ finiteBound) :
    FiniteTableUpperBound
      (externalStableKeyIntervalRowTable rows fallback)
      (classifyFiniteCutoffStableKey K) value finiteBound :=
  externalStableKeyIntervalRowTable_finiteTableUpperBound_of_keyValue
    rows fallback (classifyFiniteCutoffStableKey K) value keyValue
    (fun c => hcover (classifyFiniteCutoffCoordinate K c))
    hvalue hrow hrowUpper


end BoundedPolymerCase
end Exact3D
end StatMech
