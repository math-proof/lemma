/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary


namespace StatMech.FrontierD

noncomputable section

def fkRectColumnBandRowOne
    (R : FKRectTorus) (left right : Nat) (x : Fin R.width)
    (hleft : left <= x.val) (hright : x.val <= right) :
    FKRectColumnBandVertex R left right 1 (R.height - 1) :=
  ⟨fkRectRowOneVertex R x, by
    change left <= x.val ∧ x.val <= right ∧ 1 <= 1 ∧
      1 <= R.height - 1
    exact ⟨hleft, hright, le_rfl, by
      have hheight := R.height_gt_two
      omega⟩⟩


def fkRectColumnBandLastRow
    (R : FKRectTorus) (left right : Nat) (x : Fin R.width)
    (hleft : left <= x.val) (hright : x.val <= right) :
    FKRectColumnBandVertex R left right 1 (R.height - 1) :=
  ⟨fkRectLastRowVertex R x, by
    change left <= x.val ∧ x.val <= right ∧
      1 <= (svFinLast R.height_pos).val ∧
      (svFinLast R.height_pos).val <= R.height - 1
    refine ⟨hleft, hright, ?_, ?_⟩
    · simp [svFinLast]
      have hheight := R.height_gt_two
      omega
    · simp [svFinLast]⟩


end
end StatMech.FrontierD
