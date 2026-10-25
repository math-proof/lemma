/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part40


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem classifyByCubicRepresentative_mem {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    classifyByCubicRepresentative T hcover c ∈ T.cases :=
  (Classical.choose_spec (hcover c)).1


theorem classifyByCubicRepresentative_equivalent {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    cubicEquivalent (classifyByCubicRepresentative T hcover c) c :=
  (Classical.choose_spec (hcover c)).2


theorem cubicRepresentativeTable_covers
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T) :
    RatInterval.CaseTable.Covers T
      (classifyByCubicRepresentative T hcover) := by
  intro c
  exact classifyByCubicRepresentative_mem T hcover c


theorem cubicRepresentativeTable_sound_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r, r ∈ T.cases → (T.interval r).MemR (caseValue r)) :
    RatInterval.CaseTable.Sound T
      (classifyByCubicRepresentative T hcover) caseValue := by
  intro c
  have heq :
      caseValue c = caseValue (classifyByCubicRepresentative T hcover c) :=
    hinv (classifyByCubicRepresentative_equivalent T hcover c)
  rw [heq]
  exact hcase (classifyByCubicRepresentative T hcover c)
    (classifyByCubicRepresentative_mem T hcover c)


theorem cubicRepresentativeTable_covers_and_sound_of_cubicInvariant
    {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (caseValue : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hinv :
      ∀ {r c}, cubicEquivalent r c → caseValue c = caseValue r)
    (hcase : ∀ r, r ∈ T.cases → (T.interval r).MemR (caseValue r)) :
    RatInterval.CaseTable.Covers T
        (classifyByCubicRepresentative T hcover) ∧
      RatInterval.CaseTable.Sound T
        (classifyByCubicRepresentative T hcover) caseValue := by
  exact ⟨cubicRepresentativeTable_covers T hcover,
    cubicRepresentativeTable_sound_of_cubicInvariant
      T hcover caseValue hinv hcase⟩


end BoundedPolymerCase
end
end Exact3D
end StatMech
