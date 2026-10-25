/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalDegreeTwo_unitCharge_or_highCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (hdegree : SixVertexLocallyDegreeTwo
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.1.1
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.2.1) :
    sixVertexHorizontalDegreeTwoUnitCharge source ∨
      sixVertexHorizontalDegreeTwoHighCharge source := by
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source
  rcases sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional
      pair.1.1.2.1 pair.1.2.2.1 hdegree with hunit | hnoUnit
  · left
    exact ⟨hdegree, hunit⟩
  · right
    have homegaSector : sixVertexUpCount
        (svTorusVerticalRows T pair.1.1.1 (svFinLast T.height_pos)) =
        middle.val - 1 := by
      simpa [pair, sixVertexHorizontalLowerSector] using pair.1.1.2.2
    have hetaSector : sixVertexUpCount
        (svTorusVerticalRows T pair.1.2.1 (svFinLast T.height_pos)) =
        middle.val + 1 := by
      simpa [pair, sixVertexHorizontalUpperSector] using pair.1.2.2.2
    obtain ⟨component, hcharge⟩ :=
      exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit
        pair.1.1.2.1 pair.1.2.2.1 hdegree middle.val homegaSector
          hetaSector hmiddle_pos hnoUnit
    exact ⟨hdegree, component, hcharge⟩


theorem sixVertexHorizontalDegreeTwoUnitCharge_of_not_highCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (hdegree : SixVertexLocallyDegreeTwo
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.1.1
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.2.1)
    (hnot : ¬ sixVertexHorizontalDegreeTwoHighCharge source) :
    sixVertexHorizontalDegreeTwoUnitCharge source := by
  rcases sixVertexHorizontalDegreeTwo_unitCharge_or_highCharge source hdegree
    with hunit | hhigh
  · exact hunit
  · exact False.elim (hnot hhigh)


end
end StatMech.FrontierD
