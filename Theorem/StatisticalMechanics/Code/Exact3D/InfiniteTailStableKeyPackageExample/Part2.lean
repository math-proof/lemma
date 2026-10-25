/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackage
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part3
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


theorem rawZeroOneRows_exactKeySet (d R maxDegree maxRange : ℕ) :
    StableKeyIntervalRow.ExactKeySet
      (rawZeroOneRows d R maxDegree maxRange)
      ((exhaustiveTable d R maxDegree maxRange).image stableKey) := by
  simpa [rawZeroOneRows] using
    StableKeyIntervalRow.exactKeySet_rowsOfKeys
      ((exhaustiveTable d R maxDegree maxRange).image stableKey)
      (fun _ => zeroOneInterval)


theorem minimalCubicZeroOneRows_exactKeySet
    (d R maxDegree maxRange : ℕ) :
    StableKeyIntervalRow.ExactKeySet
      (minimalCubicZeroOneRows d R maxDegree maxRange)
      ((exhaustiveCubicClassTable d R maxDegree maxRange).image
        minimalCubicStableKey) := by
  simpa [minimalCubicZeroOneRows] using
    StableKeyIntervalRow.exactKeySet_rowsOfKeys
      ((exhaustiveCubicClassTable d R maxDegree maxRange).image
        minimalCubicStableKey)
      (fun _ => zeroOneInterval)


theorem rawZeroOneRows_cover (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    stableKey c ∈ stableKeyIntervalRowKeyFinset
      (rawZeroOneRows d R maxDegree maxRange) := by
  classical
  rw [rawZeroOneRows]
  exact
    (StableKeyIntervalRow.mem_keyFinset_rowsOfKeys _
      _ (stableKey c)).2
    (Finset.mem_image.mpr
      ⟨c, exhaustiveTable_covers d R maxDegree maxRange c, rfl⟩)


theorem minimalCubicZeroOneRows_cover (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset
      (minimalCubicZeroOneRows d R maxDegree maxRange) := by
  classical
  rw [minimalCubicZeroOneRows]
  exact
    (StableKeyIntervalRow.mem_keyFinset_rowsOfKeys _
      _
      (classifyByMinimalCubicStableKey c)).2
      (Finset.mem_image.mpr
        ⟨cubicClass c, exhaustiveCubicClassTable_covers
          d R maxDegree maxRange c, rfl⟩)


theorem rawZeroOneRows_row_sound_keyImageIndicator {d : ℕ}
    (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K))
    (row : StableKeyIntervalRow K.maxDegree K.maxRange)
    (hrow : row ∈ rawZeroOneRows d K.radius K.maxDegree K.maxRange) :
    row.interval.MemR
      (keyImageIndicator support (classifyFiniteCutoffStableKey K)
        row.key.toKey) := by
  exact StableKeyIntervalRow.memR_of_mem_rowsOfKeys
    ((exhaustiveTable d K.radius K.maxDegree K.maxRange).image stableKey)
    (fun _ => zeroOneInterval)
    (keyImageIndicator support (classifyFiniteCutoffStableKey K))
    (fun k _ =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffStableKey K) k)
    (by simpa [rawZeroOneRows] using hrow)


theorem minimalCubicZeroOneRows_row_sound_keyImageIndicator {d : ℕ}
    (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K))
    (row : StableKeyIntervalRow K.maxDegree K.maxRange)
    (hrow : row ∈ minimalCubicZeroOneRows d K.radius K.maxDegree K.maxRange) :
    row.interval.MemR
      (keyImageIndicator support
        (classifyFiniteCutoffMinimalCubicStableKey K) row.key.toKey) := by
  exact StableKeyIntervalRow.memR_of_mem_rowsOfKeys
    ((exhaustiveCubicClassTable d K.radius K.maxDegree K.maxRange).image
      minimalCubicStableKey)
    (fun _ => zeroOneInterval)
    (keyImageIndicator support
      (classifyFiniteCutoffMinimalCubicStableKey K))
    (fun k _ =>
      zeroOneInterval_memR_keyImageIndicator support
        (classifyFiniteCutoffMinimalCubicStableKey K) k)
    (by simpa [minimalCubicZeroOneRows] using hrow)


theorem rawZeroOneRows_row_upper_one (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ rawZeroOneRows d R maxDegree maxRange) :
    ((row.interval.upper : ℚ) : ℝ) ≤ 1 := by
  exact StableKeyIntervalRow.upper_le_of_mem_rowsOfKeys
    ((exhaustiveTable d R maxDegree maxRange).image stableKey)
    (fun _ => zeroOneInterval)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (by simpa [rawZeroOneRows] using hrow)


theorem minimalCubicZeroOneRows_row_upper_one
    (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ minimalCubicZeroOneRows d R maxDegree maxRange) :
    ((row.interval.upper : ℚ) : ℝ) ≤ 1 := by
  exact StableKeyIntervalRow.upper_le_of_mem_rowsOfKeys
    ((exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicStableKey)
    (fun _ => zeroOneInterval)
    (fun _ _ => zeroOneInterval_upper_le_one)
    (by simpa [minimalCubicZeroOneRows] using hrow)


end InfiniteTailStableKeyPackageExample
end Exact3D
end StatMech
