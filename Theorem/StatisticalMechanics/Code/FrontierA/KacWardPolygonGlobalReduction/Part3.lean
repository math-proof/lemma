/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part2
open scoped BigOperators
open Finset SimpleGraph Polynomial


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Ising

universe u


theorem kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_totalTurn
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D)
    (hturn :
      (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
          2 * Real.pi ∨
        (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
          -(2 * Real.pi)) :
    kwLoopPhaseProduct
        (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop =
      -1 := by
  rw [kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum]
  rcases hturn with hturn | hturn
  · rw [hturn]
    rw [show (((2 * Real.pi : ℝ) : ℂ) * Complex.I) / 2 =
      (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_pi_mul_I]
  · rw [hturn]
    rw [show ((((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I) / 2) =
      -((Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num


end StatMech.FrontierA
