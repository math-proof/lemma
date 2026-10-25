/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part36


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem exhaustiveTable_covers (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    c ∈ exhaustiveTable d R maxDegree maxRange := by
  classical
  simp [exhaustiveTable]


theorem exhaustiveTable_covers_localCoordinate {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ofLocalCoordinate c hbox hdegree hrange ∈
      exhaustiveTable d R maxDegree maxRange := by
  exact exhaustiveTable_covers d R maxDegree maxRange
    (ofLocalCoordinate c hbox hdegree hrange)


theorem exhaustiveTable_covers_diameterLocalCoordinate_after_translate
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hne : c.support.carrier.Nonempty)
    (hdiam : c.support.coordinateDiameterBound R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    ∃ (v : Site d) (bc : BoundedPolymerCase d R maxDegree maxRange),
      bc ∈ exhaustiveTable d R maxDegree maxRange ∧
        ((bc.degree : ℕ) = c.degree) ∧ ((bc.range : ℕ) = c.range) ∧
          bc.toPolymerSupport = c.support.translate v := by
  rcases exists_boundedCase_translate_of_nonempty_coordinateDiameterBound
      c hne hdiam hdegree hrange with ⟨v, bc, hdeg, hrange', hsupport⟩
  exact ⟨v, bc, exhaustiveTable_covers d R maxDegree maxRange bc,
    hdeg, hrange', hsupport⟩


theorem exhaustiveTable_covers_boundedLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    classifyBoundedLocalCoordinate c ∈
      exhaustiveTable d R maxDegree maxRange := by
  exact exhaustiveTable_covers d R maxDegree maxRange
    (classifyBoundedLocalCoordinate c)


theorem caseTable_covers_boundedLocalCoordinate_of_exhaustiveTable_subset
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hT : exhaustiveTable d R maxDegree maxRange ⊆ T.cases) :
    RatInterval.CaseTable.Covers T
      (@classifyBoundedLocalCoordinate d R maxDegree maxRange) := by
  intro c
  exact hT (exhaustiveTable_covers_boundedLocalCoordinate c)


theorem caseTable_covers_and_sound_boundedLocalCoordinate_of_caseValue
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hcover : exhaustiveTable d R maxDegree maxRange ⊆ T.cases)
    (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
    (hcase : ∀ k, k ∈ T.cases → (T.interval k).MemR (caseValue k)) :
    RatInterval.CaseTable.Covers T
        (@classifyBoundedLocalCoordinate d R maxDegree maxRange) ∧
      RatInterval.CaseTable.Sound T
        (@classifyBoundedLocalCoordinate d R maxDegree maxRange) value := by
  constructor
  · exact caseTable_covers_boundedLocalCoordinate_of_exhaustiveTable_subset
      T hcover
  · intro c
    rw [hvalue c]
    exact hcase (classifyBoundedLocalCoordinate c)
      ((caseTable_covers_boundedLocalCoordinate_of_exhaustiveTable_subset
        T hcover) c)


end BoundedPolymerCase
end
end Exact3D
end StatMech
