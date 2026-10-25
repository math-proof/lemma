/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


@[simp] theorem mem_fkRectHorizontalCutGraphEdges
    (R : FKRectTorus) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R a ∈ fkRectHorizontalCutGraphEdges R ↔
      a ∈ fkRectHorizontalCutEdges R := by
  classical
  unfold fkRectHorizontalCutGraphEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hab⟩
    exact (fkRectTorusIndexedEdge_injective R hab).symm ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩


theorem fkRectFullGraphConfiguration_eq_false_of_horizontalCutEdge
    (R : FKRectTorus) (eta : FKRectHorizontalCutClosedConfig R)
    {e : Sym2 R.Vertex} (he : e ∈ fkRectHorizontalCutGraphEdges R) :
    fkRectFullGraphConfiguration R eta.1 e = false := by
  classical
  rw [fkRectHorizontalCutGraphEdges, Finset.mem_image] at he
  rcases he with ⟨a, ha, rfl⟩
  rw [fkRectFullGraphConfiguration_indexedEdge]
  exact eta.2 a ha


end
end StatMech.FrontierD
