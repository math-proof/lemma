/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part42


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem generatedMinimalCubicRepresentativeTable_covers
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval) :
    CubicRepresentativeTableCovers
      (generatedMinimalCubicRepresentativeTable intervalOf) := by
  intro c
  refine ⟨minimalCubicRepresentative (cubicClass c), ?_, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨cubicClass c,
        exhaustiveCubicClassTable_covers d R maxDegree maxRange c, rfl⟩
  · have hclass :
        cubicClass (minimalCubicRepresentative (cubicClass c)) =
          cubicClass c :=
      minimalCubicRepresentative_class (cubicClass c)
    exact Quotient.exact hclass


theorem generatedMinimalCubicRepresentativeTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc r : BoundedPolymerCase d R maxDegree maxRange),
      r ∈ (generatedMinimalCubicRepresentativeTable intervalOf).cases ∧
        cubicEquivalent r bc ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  rcases generatedMinimalCubicRepresentativeTable_covers intervalOf bc with
    ⟨r, hrmem, hequiv⟩
  exact ⟨v, bc, r, hrmem, hequiv, hdeg, hrange', hsupport⟩


theorem generatedMinimalCubicRepresentativeTable_covers_and_sound_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r,
      r ∈ (generatedMinimalCubicRepresentativeTable intervalOf).cases →
        (intervalOf r).MemR (caseValue r)) :
    RatInterval.CaseTable.Covers
        (generatedMinimalCubicRepresentativeTable intervalOf)
        (classifyByCubicRepresentative
          (generatedMinimalCubicRepresentativeTable intervalOf)
          (generatedMinimalCubicRepresentativeTable_covers intervalOf)) ∧
      RatInterval.CaseTable.Sound
        (generatedMinimalCubicRepresentativeTable intervalOf)
        (classifyByCubicRepresentative
          (generatedMinimalCubicRepresentativeTable intervalOf)
          (generatedMinimalCubicRepresentativeTable_covers intervalOf))
        caseValue := by
  exact cubicRepresentativeTable_covers_and_sound_of_cubicInvariant
    (generatedMinimalCubicRepresentativeTable intervalOf)
    (generatedMinimalCubicRepresentativeTable_covers intervalOf)
    caseValue hinv hcase


theorem minimalRepTable_covers_and_sound_boundedLocal_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (intervalOf : BoundedPolymerCase d R maxDegree maxRange → RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r,
      r ∈ (generatedMinimalCubicRepresentativeTable intervalOf).cases →
        (intervalOf r).MemR (caseValue r)) :
    RatInterval.CaseTable.Covers
        (generatedMinimalCubicRepresentativeTable intervalOf)
        (classifyBoundedLocalCoordinateByCubicRepresentative
          (generatedMinimalCubicRepresentativeTable intervalOf)
          (generatedMinimalCubicRepresentativeTable_covers intervalOf)) ∧
      RatInterval.CaseTable.Sound
        (generatedMinimalCubicRepresentativeTable intervalOf)
        (classifyBoundedLocalCoordinateByCubicRepresentative
          (generatedMinimalCubicRepresentativeTable intervalOf)
          (generatedMinimalCubicRepresentativeTable_covers intervalOf))
        value := by
  exact cubicRepresentativeTable_covers_and_sound_boundedLocalCoordinate_of_cubicInvariant
    (generatedMinimalCubicRepresentativeTable intervalOf)
    (generatedMinimalCubicRepresentativeTable_covers intervalOf)
    value caseValue hvalue hinv hcase


end BoundedPolymerCase
end
end Exact3D
end StatMech
