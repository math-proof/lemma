/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexLexDisagreementComponentMask
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    SixVertexArrows T := by
  classical
  let seed := sixVertexLexPositiveSeamEdge T omega eta h
  let G := sixVertexTorusDisagreementGraph omega eta
  exact
    { horizontal := fun v => decide (G.Reachable seed (0, v))
      vertical := fun v => decide (G.Reachable seed (1, v)) }

end
end StatMech.FrontierD
