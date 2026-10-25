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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part5
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectLocalBoxFits (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat) : Prop :=
  upper < R.height ∧ ∀ z : FK.boxVerts 2 m,
    let p := fkRectSquareUndevelopPoint (fkRectLocalBoxPoint R center z)
    (cut : Int) <= p.1 ∧ p.1 < R.width ∧
      (lower : Int) <= p.2 ∧ p.2 <= upper


end
end StatMech.FrontierD
