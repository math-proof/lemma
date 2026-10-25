/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part41


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem cubicRepresentativeTable_covers_boundedLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T) :
    RatInterval.CaseTable.Covers T
      (classifyBoundedLocalCoordinateByCubicRepresentative T hcover) := by
  intro c
  exact classifyByCubicRepresentative_mem T hcover
    (classifyBoundedLocalCoordinate c)


theorem cubicRepresentativeTable_covers_and_sound_boundedLocalCoordinate_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, value c = caseValue (classifyBoundedLocalCoordinate c))
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r, r ∈ T.cases → (T.interval r).MemR (caseValue r)) :
    RatInterval.CaseTable.Covers T
        (classifyBoundedLocalCoordinateByCubicRepresentative T hcover) ∧
      RatInterval.CaseTable.Sound T
        (classifyBoundedLocalCoordinateByCubicRepresentative T hcover) value := by
  constructor
  · exact cubicRepresentativeTable_covers_boundedLocalCoordinate T hcover
  · intro c
    rw [hvalue c]
    have heq :
        caseValue (classifyBoundedLocalCoordinate c) =
          caseValue
            (classifyBoundedLocalCoordinateByCubicRepresentative T hcover c) :=
      hinv (classifyByCubicRepresentative_equivalent T hcover
        (classifyBoundedLocalCoordinate c))
    rw [heq]
    exact hcase (classifyBoundedLocalCoordinateByCubicRepresentative T hcover c)
      (classifyByCubicRepresentative_mem T hcover
        (classifyBoundedLocalCoordinate c))


end BoundedPolymerCase
end
end Exact3D
end StatMech
