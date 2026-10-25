/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialUnitWindingSplitHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMedialCutAlignment.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLayeredCutBalance
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part2
open Equiv


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

def FKMedialLayeredTransitionTopology
    (source : Bool -> FKMedialLoopPairing T)
    (first second : T.Vertex) : Prop :=
  (first = second /\
      (FKMedialCutSplits (source false) first <->
        Not (FKMedialCutSplits (source true) first))) \/
    (first != second /\
      FKMedialLayeredTwoCutBalanced source first second)


end
end StatMech.FrontierD
