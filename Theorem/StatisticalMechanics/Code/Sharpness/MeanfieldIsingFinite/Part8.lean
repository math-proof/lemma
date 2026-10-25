/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part8
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


theorem sct_boundaryCorr_split {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) :
    (∑ e ∈ boundaryEdges d (sctCutSites T),
      corrOriginInner d beta (sctCutSites T) e.1) =
      sctInternalBoundaryCorr d beta n T +
        sctExternalBoundaryCorr d beta n T := by
  rw [sctInternalBoundaryCorr_eq_ambient]
  unfold sctExternalBoundaryCorr
  rw [← Finset.sum_filter_add_sum_filter_not
    (boundaryEdges d (sctCutSites T)) (fun e => e.2 ∈ box d n)]


theorem sct_phiIsing_eq_tanh_mul_boundaryCorr {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) :
    phiIsing d beta (sctCutSites T) =
      Real.tanh beta *
        ∑ e ∈ boundaryEdges d (sctCutSites T),
          corrOriginInner d beta (sctCutSites T) e.1 := by
  rfl


theorem tanh_le_self_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    Real.tanh beta ≤ beta := by
  let f : ℝ → ℝ := fun x => x * Real.cosh x - Real.sinh x
  have hfderiv : ∀ x : ℝ, deriv f x = x * Real.sinh x := by
    intro x
    have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x)
    simpa [f] using hd.deriv
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    · exact ((continuous_id.mul Real.continuous_cosh).sub
        Real.continuous_sinh).continuousOn
    · exact ((differentiable_id.mul Real.differentiable_cosh).sub
        Real.differentiable_sinh).differentiableOn
    · intro x hx
      rw [interior_Ici] at hx
      rw [hfderiv]
      exact mul_nonneg (le_of_lt hx) (Real.sinh_nonneg_iff.mpr (le_of_lt hx))
  have hf := hmono (by simp) hbeta hbeta
  have hgap : Real.sinh beta ≤ beta * Real.cosh beta := by
    simpa [f] using hf
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos beta)]
  exact hgap


theorem sct_sum_currentCutMass {d n : ℕ} (beta h : ℝ) :
    (∑ T : Finset (sctBox d n),
      if sctBoxOrigin d n ∈ T then sctCurrentCutMass d beta h n T else 0) =
      1 - (sctOriginMag d beta h n) ^ 2 := by
  have hs := sum_baseCutMass_eq_one_sub_mag_sq
    (sctBoxGraph d n) beta h (sctBoxOrigin d n)
  have hspin : spinProd ({sctBoxOrigin d n} : Finset (sctBox d n)) =
      (fun s => spin s (sctBoxOrigin d n)) := by
    funext s
    simp [spinProd]
  rw [hspin] at hs
  simpa [sctCurrentCutMass, sctOriginMag, sctBoxMag] using hs


end Sharpness
end StatMech
