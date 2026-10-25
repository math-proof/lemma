/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem boundarySourceCurrentSummand_nonneg
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources : Finset V) (m : EdgeCurrent G) :
    0 ≤ if sources G (ofEdgeFun G m) ∩ interior = internalSources then
      weight G beta J (ofEdgeFun G m)
    else 0 := by
  split
  · exact Ising.acw_weight_nonneg G beta J hbeta hJ _
  · exact le_rfl

theorem summable_boundarySourceCurrentSummand
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources : Finset V) :
    Summable (fun m : EdgeCurrent G =>
      if sources G (ofEdgeFun G m) ∩ interior = internalSources then
        weight G beta J (ofEdgeFun G m)
      else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_norm_weight_ofEdgeFun G beta J)
  by_cases h : sources G (ofEdgeFun G m) ∩ interior = internalSources <;>
    simp [h]

theorem tsum_boundarySourceCurrentRawMass
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources : Finset V) :
    ∑' m : EdgeCurrent G,
        boundarySourceCurrentRawMass G beta J interior internalSources m =
      ENNReal.ofReal
        (boundarySourceCurrentSum G beta J interior internalSources) := by
  unfold boundarySourceCurrentRawMass boundarySourceCurrentSum
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · exact boundarySourceCurrentSummand_nonneg
      G beta J hbeta hJ interior internalSources
  · exact summable_boundarySourceCurrentSummand
      G beta J interior internalSources


end StatMech.FrontierB
