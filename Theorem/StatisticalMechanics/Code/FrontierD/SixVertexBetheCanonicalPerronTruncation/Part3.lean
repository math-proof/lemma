/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCanonicalLinearEdgeCutoff_pos
    {eta : Real} (heta : 0 < eta) (k : Nat) :
    0 < sixVertexCanonicalLinearEdgeCutoff eta k := by
  rw [sixVertexCanonicalLinearEdgeCutoff, Nat.ceil_pos]
  exact mul_pos heta (by
    exact_mod_cast sixVertexFourWidth_pos 0 k)

theorem sixVertexCanonicalLinearEdgeCutoff_le
    {eta : Real} (heta : eta <= 1 / 4) (k : Nat) :
    sixVertexCanonicalLinearEdgeCutoff eta k <= k + 1 := by
  rw [sixVertexCanonicalLinearEdgeCutoff, Nat.ceil_le]
  rw [sixVertexFourWidth]
  push_cast
  have hk : (0 : Real) <= (k : Real) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right heta hk]

theorem tendsto_sixVertexCanonicalLinearEdgeCutoff_ratio
    {eta : Real} (heta : 0 <= eta) :
    Tendsto (fun k : Nat =>
      (sixVertexCanonicalLinearEdgeCutoff eta k : Real) /
        (sixVertexFourWidth 0 k : Real)) atTop (nhds eta) := by
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hwidthReal : Tendsto (fun k =>
      (sixVertexFourWidth 0 k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidth
  have hinv : Tendsto (fun k =>
      (1 : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) :=
    hwidthReal.const_div_atTop 1
  have hupper : Tendsto (fun k => eta +
      (1 : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds eta) := by
    simpa using tendsto_const_nhds.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : Nat => eta) atTop (nhds eta) from
      tendsto_const_nhds) hupper
  · filter_upwards [] with k
    have hN : (0 : Real) < sixVertexFourWidth 0 k := by
      exact_mod_cast sixVertexFourWidth_pos 0 k
    rw [le_div_iff₀ hN]
    exact Nat.le_ceil
      (eta * (sixVertexFourWidth 0 k : Real))
  · filter_upwards [] with k
    have hN : (0 : Real) < sixVertexFourWidth 0 k := by
      exact_mod_cast sixVertexFourWidth_pos 0 k
    rw [div_le_iff₀ hN]
    have hceil := Nat.ceil_lt_add_one
      (mul_nonneg heta hN.le : 0 <=
        eta * (sixVertexFourWidth 0 k : Real))
    change (sixVertexCanonicalLinearEdgeCutoff eta k : Real) <=
      (eta + 1 / (sixVertexFourWidth 0 k : Real)) *
        (sixVertexFourWidth 0 k : Real)
    rw [sixVertexCanonicalLinearEdgeCutoff]
    field_simp [hN.ne']
    linarith

end
end StatMech.FrontierD
