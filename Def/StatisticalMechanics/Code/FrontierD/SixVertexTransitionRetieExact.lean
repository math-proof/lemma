module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialUnitWindingSplitHall
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMedialCutAlignment.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLayeredCutBalance
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact
open Equiv


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

noncomputable def FKMedialTwoCutSplitScore
    (pairing : FKMedialLoopPairing T) (first second : T.Vertex) : Int := by
  classical
  exact (if FKMedialCutSplits pairing first then 1 else -1) +
    (if FKMedialCutSplits (fkMedialTogglePairingAt pairing first) second
      then 1 else -1)


def FKMedialLayeredTwoCutBalanced
    (source : Bool -> FKMedialLoopPairing T)
    (first second : T.Vertex) : Prop :=
  FKMedialTwoCutSplitScore (source false) first second +
    FKMedialTwoCutSplitScore (source true) first second = 0


end
end StatMech.FrontierD
