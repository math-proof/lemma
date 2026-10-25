/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Structure.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part3


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem HexEndpointLoopGeometry.reversed_legalTurns
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (G : HexEndpointLoopGeometry region a h0 v du) :
    (ofTurns a h0 (G.base ++ anchoredLoopReverse G.loopQ)).LegalTurns := by
  have hq := G.q_valid.1.1
  have hbase : ∀ t ∈ G.base, t = 1 ∨ t = -1 := by
    intro t ht
    exact hq t (by simp [ht])
  have hloop : ∀ t ∈ G.loopQ, t = 1 ∨ t = -1 := by
    intro t ht
    exact hq t (by simp [ht])
  have hrev := anchoredLoopReverse_legal G.loopQ hloop
  intro t ht
  simp only [ofTurns_turns, List.mem_append] at ht
  rcases ht with ht | ht
  · exact hbase t ht
  · exact hrev t ht


end
end StatMech.Universality
