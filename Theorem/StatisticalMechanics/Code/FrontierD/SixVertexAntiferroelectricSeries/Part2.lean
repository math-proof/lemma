/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq]
  apply div_pos
  · exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  · positivity

theorem sixVertexFreeEnergySeriesTerm_nonneg {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    0 ≤ sixVertexFreeEnergySeriesTerm lam n := by
  unfold sixVertexFreeEnergySeriesTerm
  exact div_nonneg
    (mul_nonneg (Real.exp_nonneg _)
      (tanh_pos_of_pos (mul_pos (by positivity) hlam)).le)
    (by positivity)

theorem sixVertexFreeEnergySeriesTerm_norm_le {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ‖sixVertexFreeEnergySeriesTerm lam n‖ ≤ Real.exp (-lam) ^ (n + 1) := by
  have htanh : Real.tanh ((n + 1 : ℝ) * lam) ≤ 1 :=
    (Real.tanh_lt_one _).le
  have hden : 1 ≤ (n + 1 : ℝ) := by norm_num
  have hnum : Real.exp (-((n + 1 : ℝ) * lam)) *
      Real.tanh ((n + 1 : ℝ) * lam) ≤ Real.exp (-((n + 1 : ℝ) * lam)) := by
    exact mul_le_of_le_one_right (Real.exp_nonneg _) htanh
  have hterm : sixVertexFreeEnergySeriesTerm lam n ≤
      Real.exp (-((n + 1 : ℝ) * lam)) := by
    rw [sixVertexFreeEnergySeriesTerm, div_le_iff₀ (by positivity)]
    calc
      Real.exp (-((n + 1 : ℝ) * lam)) * Real.tanh ((n + 1 : ℝ) * lam)
          ≤ Real.exp (-((n + 1 : ℝ) * lam)) := hnum
      _ ≤ Real.exp (-((n + 1 : ℝ) * lam)) * (n + 1 : ℝ) :=
        le_mul_of_one_le_right (Real.exp_nonneg _) hden
  rw [Real.norm_eq_abs, abs_of_nonneg (sixVertexFreeEnergySeriesTerm_nonneg hlam n)]
  calc
    sixVertexFreeEnergySeriesTerm lam n
        ≤ Real.exp (-((n + 1 : ℝ) * lam)) := hterm
    _ = Real.exp (-lam) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring


theorem summable_sixVertexFreeEnergySeriesTerm {lam : ℝ} (hlam : 0 < lam) :
    Summable (sixVertexFreeEnergySeriesTerm lam) := by
  have hq0 : 0 ≤ Real.exp (-lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-lam) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => Real.exp (-lam) ^ (n + 1)) :=
    (summable_geometric_of_lt_one hq0 hq1).comp_injective Nat.succ_injective
  exact hgeom.of_norm_bounded (sixVertexFreeEnergySeriesTerm_norm_le hlam)


end StatMech.FrontierD
