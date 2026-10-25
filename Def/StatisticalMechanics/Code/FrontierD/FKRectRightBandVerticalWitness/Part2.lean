/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightBandVerticalWitness.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectRightBandRowOne
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut ≤ x.val) :
    FKRectRightStripBandVertex R cut 1 (R.height - 1) :=
  ⟨fkRectRowOneVertex R x, by
    change cut ≤ x.val ∧ 1 ≤ 1 ∧ 1 ≤ R.height - 1
    exact ⟨hx, le_rfl, by
      have hheight := R.height_gt_two
      omega⟩⟩

def fkRectRightBandLastRow
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut ≤ x.val) :
    FKRectRightStripBandVertex R cut 1 (R.height - 1) :=
  ⟨fkRectLastRowVertex R x, by
    change cut ≤ x.val ∧ 1 ≤ (svFinLast R.height_pos).val ∧
      (svFinLast R.height_pos).val ≤ R.height - 1
    refine ⟨hx, ?_, ?_⟩
    · simp [svFinLast]
      have hheight := R.height_gt_two
      omega
    · simp [svFinLast]⟩


end
end StatMech.FrontierD
