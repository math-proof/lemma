/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentLaw
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech

namespace FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem currentSummand_nonneg (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V) (m : EdgeCurrent G) :
    0 ≤ if sources G (ofEdgeFun G m) = A then weight G beta J (ofEdgeFun G m) else 0 := by
  split
  case isTrue =>
    unfold weight
    exact Finset.prod_nonneg fun e _ =>
      div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ e)) _) (Nat.cast_nonneg _)
  case isFalse => exact le_rfl


theorem tsum_currentRawMass (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V) :
    ∑' m : EdgeCurrent G, currentRawMass G beta J A m =
      ENNReal.ofReal (currentSum G beta J A) := by
  unfold currentRawMass currentSum
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · exact fun m => currentSummand_nonneg G beta J hbeta hJ A m
  · exact (summable_norm_currentSum_summand G beta J A).of_norm


end FrontierB
end StatMech
