/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
import Def.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectSquareRepresentativeVertex_vertexSquarePoint
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectSquareRepresentativeVertex R (fkRectVertexSquarePoint R x) = x := by
  rw [show fkRectVertexSquarePoint R x =
      fkRectSquareDevelopPoint ((x.1.val : Int), (x.2.val : Int)) by rfl,
    fkRectSquareRepresentativeVertex_developPoint]
  apply Prod.ext
  · exact fkRectIntModFin_natCast R.width_pos x.1
  · exact fkRectIntModFin_natCast R.height_pos x.2


end
end StatMech.FrontierD
