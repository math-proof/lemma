/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalZeroCount_eq_sum
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalZeroCount horizontal =
      ∑ v : T.Vertex,
        if sixVertexHorizontalGaugeBit horizontal v = false then 1 else 0 := by
  unfold sixVertexHorizontalZeroCount
  rw [Fintype.card_subtype, Finset.card_filter]


theorem sixVertexSwitchHorizontalPair_zeroCount
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalZeroCount
          (sixVertexSwitchHorizontalPair mask horizontal).1 +
        sixVertexHorizontalZeroCount
          (sixVertexSwitchHorizontalPair mask horizontal).2 =
      sixVertexHorizontalZeroCount horizontal.1 +
        sixVertexHorizontalZeroCount horizontal.2 := by
  simp only [sixVertexHorizontalZeroCount_eq_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  unfold sixVertexSwitchHorizontalPair sixVertexHorizontalGaugeBit
  cases hmask : mask v.1 <;> simp [hmask, add_comm]


theorem sixVertexSwitchHorizontalPair_involutive
    {T : EvenTorus} (mask : Fin T.width -> Bool) :
    Function.Involutive
      (sixVertexSwitchHorizontalPair (T := T) mask) := by
  intro horizontal
  apply Prod.ext <;> funext v
  · unfold sixVertexSwitchHorizontalPair
    cases hmask : mask v.1 <;> simp [hmask]
  · unfold sixVertexSwitchHorizontalPair
    cases hmask : mask v.1 <;> simp [hmask]

end
end StatMech.FrontierD
