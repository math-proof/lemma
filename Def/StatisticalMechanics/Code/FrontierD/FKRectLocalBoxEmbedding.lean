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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectLocalBoxPoint (R : FKRectTorus) (center : R.Vertex)
    (z : Site 2) : Int × Int :=
  ((fkRectVertexSquarePoint R center).1 + z 0,
    (fkRectVertexSquarePoint R center).2 + z 1)


def fkRectLocalBoxVertex (R : FKRectTorus) (center : R.Vertex)
    (z : Site 2) : R.Vertex :=
  fkRectSquareRepresentativeVertex R (fkRectLocalBoxPoint R center z)

end
end StatMech.FrontierD
