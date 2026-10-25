/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem summable_finiteParityKernel {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta) (odd : ↑S → Bool) :
    Summable (finiteParityKernel S beta odd) := by
  let g : E → ℕ → ℝ := fun e k =>
    if he : e ∈ S then parityEdgeKernel beta (odd ⟨e, he⟩) k
    else parityEdgeKernel beta false k
  have hg : ∀ i, Summable (g i) := by
    intro i
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : ∀ i k, 0 ≤ g i k := by
    intro i k
    unfold g
    split <;> apply parityEdgeKernel_nonneg beta hbeta
  exact (prod_tsum_fubini g hg hgnn S).1.congr (fun m => by
    unfold finiteParityKernel
    apply Fintype.prod_congr
    intro i
    simp [g])

theorem tsum_ofReal_finiteParityKernel {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta) (odd : ↑S → Bool) :
    ∑' a : ↑S → ℕ, ENNReal.ofReal (finiteParityKernel S beta odd a) = 1 := by
  let g : E → ℕ → ℝ := fun e k =>
    if he : e ∈ S then parityEdgeKernel beta (odd ⟨e, he⟩) k
    else parityEdgeKernel beta false k
  have hnonneg : ∀ a : ↑S → ℕ, 0 ≤ finiteParityKernel S beta odd a := by
    intro a
    exact Finset.prod_nonneg fun i _ =>
      parityEdgeKernel_nonneg beta hbeta (odd i) (a i)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_finiteParityKernel S beta hbeta odd)]
  have hg : ∀ i, Summable (g i) := by
    intro i
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : ∀ i k, 0 ≤ g i k := by
    intro i k
    unfold g
    split <;> apply parityEdgeKernel_nonneg beta hbeta
  rw [show (∑' a : ↑S → ℕ, finiteParityKernel S beta odd a) =
      ∑' a : ↑S → ℕ, ∏ i : ↑S, g i.1 (a i) by
    apply tsum_congr
    intro a
    simp [finiteParityKernel, g]]
  rw [← (prod_tsum_fubini g hg hgnn S).2]
  rw [← ENNReal.ofReal_one]
  apply congrArg ENNReal.ofReal
  apply Finset.prod_eq_one
  intro e he
  simp only [g, dif_pos he]
  exact tsum_parityEdgeKernel beta hbeta (odd ⟨e, he⟩)

end StatMech.FrontierB
