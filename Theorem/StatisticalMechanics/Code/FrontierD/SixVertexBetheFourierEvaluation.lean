/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFreeEnergyPairedFourierTerm_eq_seriesTerm
    (lam : Real) (n : Nat) :
    sixVertexFreeEnergyPairedFourierTerm lam n =
      sixVertexFreeEnergySeriesTerm lam n := by
  let m : Real := n + 1
  have hm : m ≠ 0 := by
    dsimp [m]
    positivity
  have hexp : Real.exp (m * lam) ≠ 0 := Real.exp_ne_zero _
  unfold sixVertexFreeEnergyPairedFourierTerm
    sixVertexFreeEnergyKernelFourierCoeff
    sixVertexRootDensityFourierCoeff
    sixVertexFreeEnergySeriesTerm
  change 2 * ((1 - Real.exp (-2 * m * lam)) / (2 * m)) *
      (1 / (2 * Real.cosh (m * lam))) =
    Real.exp (-(m * lam)) * Real.tanh (m * lam) / m
  rw [Real.cosh_eq, Real.tanh_eq]
  rw [show Real.exp (-2 * m * lam) =
      Real.exp (-(m * lam)) * Real.exp (-(m * lam)) by
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [show Real.exp (-(m * lam)) = (Real.exp (m * lam))⁻¹ by
    rw [← Real.exp_neg]]
  field_simp [hm, hexp]


end
end StatMech.FrontierD
