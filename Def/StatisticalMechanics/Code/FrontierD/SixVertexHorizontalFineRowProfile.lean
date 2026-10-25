/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalRowNontransitionCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) : Nat :=
  ∑ i : Fin T.width,
    if sixVertexHorizontalGaugeBit horizontal
          (SixVertexArrows.cyclicPred T.width_pos i, j) =
        sixVertexHorizontalGaugeBit horizontal (i, j)
    then 1 else 0


def sixVertexHorizontalPairRowNontransitionProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Fin T.height -> Nat :=
  fun j => sixVertexHorizontalRowNontransitionCount horizontal.1 j +
    sixVertexHorizontalRowNontransitionCount horizontal.2 j


def sixVertexHorizontalPairFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Fin T.height -> Nat × Nat :=
  fun j =>
    (sixVertexHorizontalPairRowNontransitionProfile horizontal j,
      sixVertexHorizontalPairRowZeroProfile horizontal j)

end
end StatMech.FrontierD
