/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalColumnClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part9
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalFreeColumns
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Finset (Fin T.width) :=
  Finset.univ.filter fun i => forall j,
    horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) =
      horizontal (i, j)


def sixVertexVerticalConstantColumnCompletion
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (i : Fin T.width)
    (hfree : forall j,
      horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) =
        horizontal (i, j))
    (seam : Bool) :
    SixVertexVerticalColumnCompletion T horizontal i :=
  ⟨fun _ => seam, fun j => by
    rw [hfree j]
    cases horizontal (i, j) <;> cases seam <;> simp⟩

end
end StatMech.FrontierD
