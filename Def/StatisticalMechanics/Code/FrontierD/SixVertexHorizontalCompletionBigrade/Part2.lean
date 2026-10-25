/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexSectorConfigurationEquivHorizontalCompletion
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    SixVertexMarkedSectorConfiguration T sector ≃
      Sigma (SixVertexHorizontalSectorCompletion T sector) where
  toFun omega :=
    ⟨omega.1.horizontal,
      ⟨⟨omega.1.vertical, omega.2.1⟩, omega.2.2⟩⟩
  invFun completed :=
    ⟨sixVertexArrowsOfFields completed.1 completed.2.1.1,
      completed.2.1.2, completed.2.2⟩
  left_inv omega := by
    apply Subtype.ext
    apply SixVertexArrows.ext <;> rfl
  right_inv completed := by
    rcases completed with ⟨horizontal, ⟨⟨vertical, hice⟩, hsector⟩⟩
    rfl


def sixVertexHorizontalGaugeBit
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (v : T.Vertex) : Bool :=
  horizontal v ^^ fkMedialVertexParity v

def sixVertexHorizontalZeroCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) : Nat :=
  Fintype.card {v : T.Vertex //
    sixVertexHorizontalGaugeBit horizontal v = false}

def sixVertexHorizontalNontransitionCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) : Nat :=
  ∑ v, if sixVertexHorizontalGaugeBit horizontal
          (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
        sixVertexHorizontalGaugeBit horizontal v then 1 else 0


def sixVertexHorizontalPairBigrade
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Nat × Nat :=
  (sixVertexHorizontalNontransitionCount horizontal.1 +
      sixVertexHorizontalNontransitionCount horizontal.2,
    2 * (sixVertexHorizontalZeroCount horizontal.1 +
      sixVertexHorizontalZeroCount horizontal.2))

end
end StatMech.FrontierD
