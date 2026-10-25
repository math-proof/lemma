/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierDensity
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem summable_sixVertexFourierRootDensityMajorant
    {lam : Real} (hlam : 0 < lam) :
    Summable (sixVertexFourierRootDensityMajorant lam) := by
  have hq0 : 0 <= Real.exp (-lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeom : Summable (fun n : Nat => Real.exp (-lam) ^ (n + 1)) :=
    (summable_geometric_of_lt_one hq0 hq1).comp_injective Nat.succ_injective
  simpa [sixVertexFourierRootDensityMajorant] using Summable.mul_left 2 hgeom

theorem norm_sixVertexFourierRootDensityTerm_le
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) :
    ‖sixVertexFourierRootDensityTerm lam n alpha‖ <=
      sixVertexFourierRootDensityMajorant lam n := by
  let m : Real := n + 1
  let x : Real := m * lam
  have hm : 0 < m := by
    dsimp [m]
    positivity
  have hx : 0 < x := mul_pos hm hlam
  have hcos : |Real.cos (m * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hcosh : Real.exp x <= 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-x)]
  have hinv : 1 / Real.cosh x <= 2 * Real.exp (-x) := by
    have hhalf : 1 / (2 * Real.cosh x) <= 1 / Real.exp x :=
      one_div_le_one_div_of_le (Real.exp_pos x) hcosh
    calc
      1 / Real.cosh x = 2 * (1 / (2 * Real.cosh x)) := by
        field_simp [(Real.cosh_pos x).ne']
      _ <= 2 * (1 / Real.exp x) := by gcongr
      _ = 2 * Real.exp (-x) := by
        simp [div_eq_mul_inv, Real.exp_neg]
  have hterm :
      |Real.cos (m * alpha)| / Real.cosh x <= 2 * Real.exp (-x) :=
    (div_le_div_of_nonneg_right hcos (Real.cosh_pos x).le).trans hinv
  rw [sixVertexFourierRootDensityTerm, Real.norm_eq_abs, abs_div,
    abs_of_pos (Real.cosh_pos _)]
  change |Real.cos (m * alpha)| / Real.cosh x <= _
  calc
    |Real.cos (m * alpha)| / Real.cosh x <= 2 * Real.exp (-x) := hterm
    _ = sixVertexFourierRootDensityMajorant lam n := by
      rw [sixVertexFourierRootDensityMajorant]
      dsimp [x, m]
      rw [<- Real.exp_nat_mul]
      congr 2
      push_cast
      ring

theorem summable_sixVertexFourierRootDensityTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexFourierRootDensityTerm lam n alpha) :=
  (summable_sixVertexFourierRootDensityMajorant hlam).of_norm_bounded
    (fun n => norm_sixVertexFourierRootDensityTerm_le hlam n alpha)


end
end StatMech.FrontierD
