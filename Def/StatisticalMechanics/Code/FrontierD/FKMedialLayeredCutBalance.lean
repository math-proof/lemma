/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLayeredCutBalance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMedialCutAlignment.Part2


namespace StatMech.FrontierD

noncomputable section

def FKMedialLayeredTwoCutBalance
    {T : EvenTorus} (source : Bool -> FKMedialLoopPairing T)
    (first second : T.Vertex) : Prop :=
  (FKMedialCutSplits (source false) first <->
      Not (FKMedialCutSplits (source true) first)) /\
    (FKMedialCutSplits
        (fkMedialTogglePairingAt (source false) first) second <->
      Not (FKMedialCutSplits
        (fkMedialTogglePairingAt (source true) first) second))


end
end StatMech.FrontierD
