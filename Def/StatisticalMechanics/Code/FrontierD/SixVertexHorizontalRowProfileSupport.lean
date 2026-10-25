/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalRowZeroCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) : Nat :=
  ∑ i : Fin T.width,
    if sixVertexHorizontalGaugeBit horizontal (i, j) = false then 1 else 0


def sixVertexHorizontalPairRowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Fin T.height -> Nat :=
  fun j => sixVertexHorizontalRowZeroCount horizontal.1 j +
    sixVertexHorizontalRowZeroCount horizontal.2 j

end
end StatMech.FrontierD
