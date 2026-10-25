/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPositiveEvenHeight_pos (M : Nat) :
    0 < sixVertexPositiveEvenHeight M := by
  simp [sixVertexPositiveEvenHeight]

theorem sixVertexPositiveEvenHeight_even (M : Nat) :
    Even (sixVertexPositiveEvenHeight M) := by
  exact ⟨M + 1, by simp [sixVertexPositiveEvenHeight, two_mul]⟩

theorem tendsto_sixVertexPositiveEvenHeight :
    Tendsto sixVertexPositiveEvenHeight atTop atTop := by
  refine tendsto_atTop.2 (fun N => ?_)
  filter_upwards [eventually_ge_atTop N] with M hM
  unfold sixVertexPositiveEvenHeight
  omega


end
end StatMech.FrontierD
