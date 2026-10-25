/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem summable_parityCurrentKernel (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) :
    Summable (parityCurrentKernel G beta H) := by
  let g : Sym2 V → ℕ → ℝ := fun e k =>
    parityEdgeKernel beta (e ∈ H) k
  have hg : ∀ e, Summable (g e) := fun e =>
    summable_parityEdgeKernel beta (e ∈ H)
  have hgnn : ∀ e k, 0 ≤ g e k := fun e k =>
    parityEdgeKernel_nonneg beta hbeta (e ∈ H) k
  exact (prod_tsum_fubini g hg hgnn G.edgeFinset).1.congr (fun m => rfl)

theorem tsum_ofReal_parityCurrentKernel (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) :
    ∑' m : EdgeCurrent G, ENNReal.ofReal (parityCurrentKernel G beta H m) = 1 := by
  have hnonneg : ∀ m : EdgeCurrent G,
      0 ≤ parityCurrentKernel G beta H m := by
    intro m
    unfold parityCurrentKernel
    exact Finset.prod_nonneg fun e _ =>
      parityEdgeKernel_nonneg beta hbeta (e.1 ∈ H) (m e)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_parityCurrentKernel G beta hbeta H),
    tsum_parityCurrentKernel G beta hbeta H]
  simp

end StatMech.FrontierB
