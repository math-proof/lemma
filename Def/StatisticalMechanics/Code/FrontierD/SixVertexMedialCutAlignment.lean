/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKMedialCutSplits
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) : Prop :=
  (fkMedialLoopGraph T pairing).Reachable
  (fkMedialWestDart v) (fkMedialEastDart v)


end
end StatMech.FrontierD
