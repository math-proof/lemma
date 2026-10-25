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
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part11


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

def HexEndpointLoopGeometry.toPair
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (G : HexEndpointLoopGeometry region a h0 v du)
    (hUmlaufsatz : G.loopQ.sum = -4) :
    HexEndpointLoopPair region a h0 v du where
  base := G.base
  loopQ := G.loopQ
  loopQ_sum := hUmlaufsatz
  q_valid := G.q_valid
  r_valid :=
    ⟨⟨G.reversed_legalTurns, G.reversed_saw⟩,
      G.reversed_stay, G.reversed_ends⟩


def HexEndpointLoopPair.piece
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (P : HexEndpointLoopPair region a h0 v du) : Finset (List ℤ) :=
  {P.base ++ P.loopQ, P.base ++ anchoredLoopReverse P.loopQ}


end
end StatMech.Universality
