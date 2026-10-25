/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingRankTwoInsertion
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectWalkWinding_concat_eq_add_step
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y z : R.Vertex} (p : G.Walk x y) (h : G.Adj y z) :
    fkRectWalkWinding R (p.concat h) =
      fkRectWalkWinding R p + fkRectStepWinding R y z := by
  rw [fkRectWalkWinding_concat]
  rfl


end
end StatMech.FrontierD
