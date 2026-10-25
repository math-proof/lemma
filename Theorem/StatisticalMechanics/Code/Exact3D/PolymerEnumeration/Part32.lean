/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part38


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem generatedStableKeyIntervalTable_covers_boundedCase
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable.Covers
      (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf)
      (@stableKey d R maxDegree maxRange) := by
  intro c
  exact Finset.mem_image.mpr
    ⟨c, exhaustiveTable_covers d R maxDegree maxRange c, rfl⟩


theorem generatedStableKeyIntervalTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      stableKey bc ∈
          (generatedStableKeyIntervalTable
            (d := d) (R := R) intervalOf).cases ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  exact ⟨v, bc,
    (generatedStableKeyIntervalTable_covers_boundedCase intervalOf) bc,
    hdeg, hrange', hsupport⟩


theorem generatedStableKeyIntervalTable_sound_boundedCase_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hvalue : ∀ c, caseValue c = keyValue (stableKey c))
    (hkey : ∀ k,
      k ∈ (generatedStableKeyIntervalTable
          (d := d) (R := R) intervalOf).cases →
        (intervalOf k).MemR (keyValue k)) :
    RatInterval.CaseTable.Sound
      (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf)
      (@stableKey d R maxDegree maxRange) caseValue := by
  intro c
  rw [hvalue c]
  exact hkey (stableKey c)
    ((generatedStableKeyIntervalTable_covers_boundedCase
      (d := d) (R := R) intervalOf) c)


theorem generatedStableKeyTable_covers_and_sound_boundedLocal_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hvalue : ∀ c,
      value c = keyValue (stableKey (classifyBoundedLocalCoordinate c)))
    (hkey : ∀ k,
      k ∈ (generatedStableKeyIntervalTable
          (d := d) (R := R) intervalOf).cases →
        (intervalOf k).MemR (keyValue k)) :
    RatInterval.CaseTable.Covers
        (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c)) ∧
      RatInterval.CaseTable.Sound
        (generatedStableKeyIntervalTable (d := d) (R := R) intervalOf)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c)) value := by
  constructor
  · intro c
    exact (generatedStableKeyIntervalTable_covers_boundedCase
      (d := d) (R := R) intervalOf) (classifyBoundedLocalCoordinate c)
  · intro c
    rw [hvalue c]
    exact hkey (stableKey (classifyBoundedLocalCoordinate c))
      ((generatedStableKeyIntervalTable_covers_boundedCase
        (d := d) (R := R) intervalOf) (classifyBoundedLocalCoordinate c))


end BoundedPolymerCase
end
end Exact3D
end StatMech
