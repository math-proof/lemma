/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem generatedCubicIntervalTable_covers_boundedCase
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable.Covers
      (generatedCubicIntervalTable intervalOf)
      (@cubicClass d R maxDegree maxRange) := by
  intro c
  exact exhaustiveCubicClassTable_covers d R maxDegree maxRange c


theorem generatedCubicIntervalTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval)
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      cubicClass bc ∈ (generatedCubicIntervalTable intervalOf).cases ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  exact ⟨v, bc, (generatedCubicIntervalTable_covers_boundedCase intervalOf) bc,
    hdeg, hrange', hsupport⟩


theorem generatedCubicIntervalTable_covers_boundedLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable.Covers
      (generatedCubicIntervalTable intervalOf)
      (@classifyBoundedLocalCoordinateCubicClass d R maxDegree maxRange) := by
  intro c
  exact exhaustiveCubicClassTable_covers d R maxDegree maxRange
    (classifyBoundedLocalCoordinate c)


theorem generatedCubicIntervalTable_sound_boundedCase_of_classValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (classValue : CubicClass d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, caseValue c = classValue (cubicClass c))
    (hclass : ∀ q, (intervalOf q).MemR (classValue q)) :
    RatInterval.CaseTable.Sound
      (generatedCubicIntervalTable intervalOf)
      (@cubicClass d R maxDegree maxRange) caseValue := by
  intro c
  rw [hvalue c]
  exact hclass (cubicClass c)


theorem generatedCubicIntervalTable_covers_and_sound_boundedLocalCoordinate_of_classValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : CubicClass d R maxDegree maxRange → RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (classValue : CubicClass d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c,
      value c = classValue (classifyBoundedLocalCoordinateCubicClass c))
    (hclass : ∀ q, (intervalOf q).MemR (classValue q)) :
    RatInterval.CaseTable.Covers
        (generatedCubicIntervalTable intervalOf)
        (@classifyBoundedLocalCoordinateCubicClass d R maxDegree maxRange) ∧
      RatInterval.CaseTable.Sound
        (generatedCubicIntervalTable intervalOf)
        (@classifyBoundedLocalCoordinateCubicClass d R maxDegree maxRange) value := by
  constructor
  · exact generatedCubicIntervalTable_covers_boundedLocalCoordinate intervalOf
  · intro c
    rw [hvalue c]
    exact hclass (classifyBoundedLocalCoordinateCubicClass c)


end BoundedPolymerCase
end
end Exact3D
end StatMech
