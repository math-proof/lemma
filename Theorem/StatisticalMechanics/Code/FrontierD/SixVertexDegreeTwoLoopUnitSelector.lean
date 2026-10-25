/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoLoopUnitSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoLoopUnitSelector


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalDegreeTwoLoop_unitSelector_or_highCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1.1.1 source.1.1.2.1) :
    Nonempty (SixVertexHorizontalDegreeTwoLoopUnitSelector source) ∨
      sixVertexHorizontalDegreeTwoLoopHighCharge source := by
  rcases sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional
      source.1.1.1.2.1 source.1.1.2.2.1 hdegree with hunit | hnoUnit
  · left
    obtain ⟨component, hcharge⟩ := hunit
    exact ⟨⟨hdegree, component, hcharge⟩⟩
  · right
    have homegaSector : sixVertexUpCount
        (svTorusVerticalRows T source.1.1.1.1 (svFinLast T.height_pos)) =
        middle.val - 1 := by
      simpa [sixVertexHorizontalLowerSector] using source.1.1.1.2.2
    have hetaSector : sixVertexUpCount
        (svTorusVerticalRows T source.1.1.2.1 (svFinLast T.height_pos)) =
        middle.val + 1 := by
      simpa [sixVertexHorizontalUpperSector] using source.1.1.2.2.2
    obtain ⟨component, hcharge⟩ :=
      exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit
        source.1.1.1.2.1 source.1.1.2.2.1 hdegree middle.val homegaSector
          hetaSector hmiddle_pos hnoUnit
    exact ⟨hdegree, component, hcharge⟩


theorem sixVertexHorizontalDegreeTwoLoopUnitSelector_nonempty_of_not_high
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1.1.1 source.1.1.2.1)
    (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source) :
    Nonempty (SixVertexHorizontalDegreeTwoLoopUnitSelector source) := by
  rcases sixVertexHorizontalDegreeTwoLoop_unitSelector_or_highCharge
      source hdegree with hunit | hhigh
  · exact hunit
  · exact False.elim (hnon hhigh)


end
end StatMech.FrontierD
