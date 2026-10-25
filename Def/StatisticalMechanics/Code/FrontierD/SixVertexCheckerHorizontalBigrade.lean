/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCheckerHorizontalBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexArrowPairBigradeAlignment.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexCheckerHorizontalBit
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  omega.horizontal v ^^ fkMedialVertexParity v

def sixVertexCheckerHorizontalZeroCount
    {T : EvenTorus} (omega : SixVertexArrows T) : Nat :=
  Fintype.card {v : T.Vertex //
    sixVertexCheckerHorizontalBit omega v = false}

def sixVertexCheckerHorizontalNontransitionCount
    {T : EvenTorus} (omega : SixVertexArrows T) : Nat :=
  ∑ v, if sixVertexCheckerHorizontalBit omega
          (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
        sixVertexCheckerHorizontalBit omega v then 1 else 0

end
end StatMech.FrontierD
