/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentTightness
import Def.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem boundaryCurrentSummand_nonneg (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (m : EdgeCurrent G) :
    0 ≤ if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
      weight G beta J (ofEdgeFun G m) else 0 := by
  split
  · unfold weight
    exact Finset.prod_nonneg fun e _ =>
      div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ e)) _) (Nat.cast_nonneg _)
  · exact le_rfl


theorem summable_boundaryCurrentSummand (beta : ℝ) (J : Sym2 V → ℝ)
    (interior : Finset V) :
    Summable (fun m : EdgeCurrent G =>
      if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
        weight G beta J (ofEdgeFun G m) else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_norm_weight_ofEdgeFun G beta J)
  by_cases h : (sources G (ofEdgeFun G m)) ∩ interior = ∅ <;> simp [h]


theorem tsum_boundaryCurrentRawMass (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    ∑' m : EdgeCurrent G, boundaryCurrentRawMass G beta J interior m =
      ENNReal.ofReal (boundaryCurrentSum G beta J interior) := by
  unfold boundaryCurrentRawMass boundaryCurrentSum
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · exact fun m => boundaryCurrentSummand_nonneg G beta J hbeta hJ interior m
  · exact summable_boundaryCurrentSummand G beta J interior


theorem one_le_boundaryCurrentSum (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    1 ≤ boundaryCurrentSum G beta J interior := by
  unfold boundaryCurrentSum
  have hs := summable_boundaryCurrentSummand G beta J interior
  calc
    1 = (if (sources G (ofEdgeFun G (0 : EdgeCurrent G))) ∩ interior = ∅ then
        weight G beta J (ofEdgeFun G (0 : EdgeCurrent G)) else 0) := by
      rw [if_pos]
      · rw [weight_ofEdgeFun]
        simp
      · simp [sources_zero_current G]
    _ ≤ ∑' m : EdgeCurrent G,
        if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
          weight G beta J (ofEdgeFun G m) else 0 :=
      hs.le_tsum (0 : EdgeCurrent G) (fun m _ =>
        boundaryCurrentSummand_nonneg G beta J hbeta hJ interior m)


end StatMech.FrontierB
