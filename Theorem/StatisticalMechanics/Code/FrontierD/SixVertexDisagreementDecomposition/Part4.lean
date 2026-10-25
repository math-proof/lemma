/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLexPositiveSeamEdge_disagrees
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    sixVertexTorusEdgeDisagrees omega eta
      (sixVertexLexPositiveSeamEdge T omega eta h) := by
  have hm := sixVertexLexPositiveSeamSeed_mem T omega eta h
  simp only [sixVertexPositiveSeamDisagreements, Finset.mem_filter,
    Finset.mem_univ, true_and] at hm
  simp [sixVertexLexPositiveSeamEdge, sixVertexTorusEdgeDisagrees,
    sixVertexTorusEdgeArrow, hm.1, hm.2]


end
end StatMech.FrontierD
