/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in

theorem spinProd_le_one (A : Finset V) (s : ConfigSpace V) : spinProd A s ≤ 1 := by
  classical
  have hpm : spinProd A s = 1 ∨ spinProd A s = -1 := by
    induction A using Finset.induction with
    | empty => simp [spinProd]
    | @insert a A ha ih =>
      rw [spinProd, Finset.prod_insert ha]
      change spin s a * spinProd A s = 1 ∨ spin s a * spinProd A s = -1
      rcases spin_eq_pm s a with hs | hs <;>
        rcases ih with hA | hA <;> simp [hs, hA]
  rcases hpm with h | h
  · rw [h]
  · rw [h]
    norm_num


theorem expectationJ_le_one (beta : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    expectationJ G beta J A ≤ 1 := by
  unfold expectationJ
  apply (div_le_one (partitionJ_pos G beta J)).2
  unfold partitionJ
  apply Finset.sum_le_sum
  intro s hs
  exact mul_le_of_le_one_left (boltzmannJ_pos G beta J s).le (spinProd_le_one A s)


theorem currentSum_le_empty (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V) :
    currentSum G beta J A ≤ currentSum G beta J ∅ := by
  rw [Ising.acr_eq15_insertion']
  exact mul_le_of_le_one_left
    (Ising.acr_currentSum_nonneg G beta J hbeta hJ ∅)
    (expectationJ_le_one G beta J A)


end StatMech.FrontierB
