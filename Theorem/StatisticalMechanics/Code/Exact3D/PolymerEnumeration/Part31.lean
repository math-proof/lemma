/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part37


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem generatedIntervalTable_covers {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable.Covers
      (generatedIntervalTable intervalOf) id := by
  intro c
  exact exhaustiveTable_covers d R maxDegree maxRange c


theorem generatedIntervalTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      bc ∈ (generatedIntervalTable intervalOf).cases ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  exact ⟨v, bc, (generatedIntervalTable_covers intervalOf) bc,
    hdeg, hrange', hsupport⟩


theorem generatedIntervalTable_sound_of_caseValue {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hcase : ∀ c, (intervalOf c).MemR (caseValue c)) :
    RatInterval.CaseTable.Sound
      (generatedIntervalTable intervalOf) id caseValue := by
  intro c
  exact hcase c


theorem generatedIntervalTable_covers_and_sound_boundedLocalCoordinate_of_caseValue
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
    (hcase : ∀ c, (intervalOf c).MemR (caseValue c)) :
    RatInterval.CaseTable.Covers
        (generatedIntervalTable intervalOf)
        (@classifyBoundedLocalCoordinate d R maxDegree maxRange) ∧
      RatInterval.CaseTable.Sound
        (generatedIntervalTable intervalOf)
        (@classifyBoundedLocalCoordinate d R maxDegree maxRange) value := by
  constructor
  · intro c
    exact exhaustiveTable_covers_boundedLocalCoordinate c
  · intro c
    rw [hvalue c]
    exact hcase (classifyBoundedLocalCoordinate c)


end BoundedPolymerCase
end
end Exact3D
end StatMech
