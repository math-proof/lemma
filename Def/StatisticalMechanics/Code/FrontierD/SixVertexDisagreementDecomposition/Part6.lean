/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusMaskSelects
    {T : EvenTorus} (mask : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : Bool :=
  if e.1 = 0 then mask.horizontal e.2 else mask.vertical e.2

end
end StatMech.FrontierD
