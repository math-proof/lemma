/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton


namespace StatMech.FrontierD

theorem sixVertexFourByFourAudited_nextVerticalRow_eq_of_ice
    (below current horizontal : SixVertexRow 4)
    (hice : svHorizontalIce (by norm_num) below current horizontal) :
    sixVertexFourByFourNextVerticalRow horizontal below = current := by
  funext x
  have hx := hice x
  unfold svHorizontalIce svHorizontalIncomingCount at hx
  unfold sixVertexFourByFourNextVerticalRow
  generalize horizontal (SixVertexArrows.cyclicPred (by norm_num) x) = a at hx ⊢
  generalize horizontal x = b at hx ⊢
  generalize below x = c at hx ⊢
  generalize current x = d at hx ⊢
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

end StatMech.FrontierD
