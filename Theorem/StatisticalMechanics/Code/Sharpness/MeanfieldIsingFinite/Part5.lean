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
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part5
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


theorem sctEdgeCutMass_eq_sum_boundary {d n : ℕ} (beta h : ℝ)
    (e : Sym2 (sctBox d n)) :
    sctEdgeCutMass d beta h n e =
      ∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T then
          sctEdgeBoundaryCorr beta T e * sctCurrentCutMass d beta h n T
        else 0 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [sctEdgeCutMass_mk]
      unfold sctOrientedCutMass
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T _
      by_cases ho : sctBoxOrigin d n ∈ T <;>
        by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;>
        simp [ho, hx, hy, sctEdgeBoundaryCorr] <;> ring


theorem sct_sum_edgeCutMass_eq_sum_internalBoundary {d n : ℕ} (beta h : ℝ) :
    (∑ e ∈ (sctBoxGraph d n).edgeFinset, sctEdgeCutMass d beta h n e) =
      ∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T then
          sctInternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
        else 0 := by
  simp_rw [sctEdgeCutMass_eq_sum_boundary beta h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  by_cases ho : sctBoxOrigin d n ∈ T
  · rw [if_pos ho]
    unfold sctInternalBoundaryCorr
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    rw [if_pos ho]
  · rw [if_neg ho]
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg ho]


theorem sctCutSites_subset_box {d n : ℕ} (T : Finset (sctBox d n)) :
    (sctCutSites T : Set (Site d)) ⊆ box d n := by
  intro z hz
  change z ∈ sctCutSites T at hz
  rw [sctCutSites, Finset.mem_image] at hz
  obtain ⟨x, _, rfl⟩ := hz
  exact x.2


end Sharpness
end StatMech
