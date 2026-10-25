/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4
import Mathlib.Analysis.Real.Pi.Wallis
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem tendsto_sixVertexCanonicalOddZeroPrefactorNormalized
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (sixVertexCanonicalOddZeroPrefactorNormalized hc s) atTop
      (nhds (c ^ 2 * (2 * Real.pi) *
        sixVertexFourierPhysicalDensity c hc 0)) := by
  have hdensity := tendsto_sixVertexCanonicalOddFiniteDensity_zero hc s
  have hmul := hdensity.const_mul (c ^ 2 * (2 * Real.pi))
  apply hmul.congr'
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  symm
  unfold sixVertexCanonicalOddZeroPrefactorNormalized
  rw [sixVertexCanonicalOddZeroPrefactor_eq_finiteDensity hc s k hk]
  have hN : (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  field_simp [hN]

theorem sixVertexCanonicalOddZeroPrefactorNormalized_limit_pos
    {c : Real} (hc : 2 < c) :
    0 < c ^ 2 * (2 * Real.pi) *
      sixVertexFourierPhysicalDensity c hc 0 := by
  exact mul_pos (mul_pos (sq_pos_of_pos (by linarith))
    (mul_pos (by norm_num) Real.pi_pos))
    (sixVertexFourierPhysicalDensity_pos hc 0)

theorem tendsto_log_sixVertexCanonicalOddZeroPrefactorNormalized
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => Real.log
      (sixVertexCanonicalOddZeroPrefactorNormalized hc s k)) atTop
      (nhds (Real.log (c ^ 2 * (2 * Real.pi) *
        sixVertexFourierPhysicalDensity c hc 0))) := by
  exact (Real.continuousAt_log
    (sixVertexCanonicalOddZeroPrefactorNormalized_limit_pos hc).ne').tendsto.comp
      (tendsto_sixVertexCanonicalOddZeroPrefactorNormalized hc s)

end
end StatMech.FrontierD
