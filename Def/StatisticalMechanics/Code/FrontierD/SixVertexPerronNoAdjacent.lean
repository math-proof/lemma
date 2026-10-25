/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronNoAdjacent
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledTransferInfinityVector
    (N n : Nat) (hhalf : 2 * n = N) : SixVertexSector N n → Real :=
  fun x => if x = sixVertexAlternatingEvenSector N n hhalf.le ∨
      x = sixVertexAlternatingOddSector N n hhalf.le then 1 else 0


end
end StatMech.FrontierD
