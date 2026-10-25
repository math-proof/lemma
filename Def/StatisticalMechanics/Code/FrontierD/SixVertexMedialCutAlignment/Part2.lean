/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMedialCutAlignment
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKMedialAlternatingTwoCut
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex) : Prop :=
  FKMedialCutSplits pairing first ↔
    ¬FKMedialCutSplits (fkMedialTogglePairingAt pairing first) second


end
end StatMech.FrontierD
