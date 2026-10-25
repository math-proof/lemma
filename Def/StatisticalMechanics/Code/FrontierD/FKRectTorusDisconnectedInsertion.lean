/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingRankTwoInsertion
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisconnectedInsertion
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectGraphClosedWindingSubgroup (R : FKRectTorus)
    (G : SimpleGraph R.Vertex) (x : R.Vertex) :
    AddSubgroup (Int × Int) where
  carrier := {u | ∃ p : G.Walk x x, fkRectWalkWinding R p = u}
  zero_mem' := ⟨.nil, rfl⟩
  add_mem' := by
    rintro u v ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p.append q, fkRectWalkWinding_append R p q⟩
  neg_mem' := by
    rintro u ⟨p, rfl⟩
    exact ⟨p.reverse, fkRectWalkWinding_reverse R p⟩


end
end StatMech.FrontierD
