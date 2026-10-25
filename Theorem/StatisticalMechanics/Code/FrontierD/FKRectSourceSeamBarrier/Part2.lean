/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBarrierConnectionProduct
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part2


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectAllButOneOpenSeamEvent_iff
    (R : FKRectTorus) (gap : R.EdgeIndex) (omega : R.Configuration) :
    omega ∈ fkRectAllButOneOpenSeamEvent R gap ↔
      ∀ a ∈ fkRectHorizontalCutEdges R, omega a = decide (a ≠ gap) :=
  Iff.rfl

theorem fkRectAllButOneOpenSeamEvent_open_iff
    (R : FKRectTorus) {gap : R.EdgeIndex} {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
    {a : R.EdgeIndex} (ha : a ∈ fkRectHorizontalCutEdges R) :
    omega a = true ↔ a ≠ gap := by
  rw [homega a ha]
  simp [fkRectAllButOneOpenConfiguration]

theorem fkRectAllButOneOpenSeamEvent_gap_closed
    (R : FKRectTorus) {gap : R.EdgeIndex}
    (hgap : gap ∈ fkRectHorizontalCutEdges R)
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
    omega gap = false := by
  rw [homega gap hgap]
  simp [fkRectAllButOneOpenConfiguration]


end
end StatMech.FrontierD
