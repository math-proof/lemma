/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part10


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

@[simp] theorem externalStableKeyIntervalRowTable_cases
    {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) :
    (externalStableKeyIntervalRowTable rows fallback).cases =
      stableKeyIntervalRowKeyFinset rows :=
  rfl

@[simp] theorem externalStableKeyIntervalRowTable_interval
    {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) (k : StableKey maxDegree maxRange) :
    (externalStableKeyIntervalRowTable rows fallback).interval k =
      intervalOfRows rows fallback k :=
  rfl


theorem externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
    {α : Type*} {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hcover : ∀ a, classifier a ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable rows fallback) classifier ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable rows fallback) classifier value := by
  exact externalStableKeyIntervalTable_covers_and_sound_of_keyValue
    (stableKeyIntervalRowRecords rows) (intervalOfRows rows fallback)
    classifier value keyValue hcover hvalue
    (fun k hk => intervalOfRows_memR_of_mem_keyFinset rows fallback keyValue hrow hk)


theorem externalStableKeyIntervalRowTable_covers_and_sound_of_exactKeySet
    {α : Type*} {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey maxDegree maxRange))
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ a, classifier a ∈ expected)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable rows fallback) classifier ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable rows fallback) classifier value := by
  exact externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
    rows fallback classifier value keyValue
    (StableKeyIntervalRow.classifier_mem_rows_of_exactKeySet
      hexact classifier hcover)
    hvalue hrow


theorem externalStableKeyIntervalRows_covers_and_sound_boundedLocal_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hcover : ∀ c : BoundedPolymerCase d R maxDegree maxRange,
      stableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      value c = keyValue (stableKey (classifyBoundedLocalCoordinate c)))
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable rows fallback)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c)) ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable rows fallback)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c)) value := by
  exact externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
    rows fallback
    (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
      stableKey (classifyBoundedLocalCoordinate c))
    value keyValue
    (fun c => hcover (classifyBoundedLocalCoordinate c))
    hvalue hrow


theorem externalStableKeyIntervalRows_covers_and_sound_minimalCubicBoundedLocal_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hcover : ∀ c : BoundedPolymerCase d R maxDegree maxRange,
      classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      value c =
        keyValue (classifyByMinimalCubicStableKey
          (classifyBoundedLocalCoordinate c)))
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable rows fallback)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable rows fallback)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) value := by
  exact externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
    rows fallback
    (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
      classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c))
    value keyValue
    (fun c => hcover (classifyBoundedLocalCoordinate c))
    hvalue hrow

end BoundedPolymerCase
end Exact3D
end StatMech
