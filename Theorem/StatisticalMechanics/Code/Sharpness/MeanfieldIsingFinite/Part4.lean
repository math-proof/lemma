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
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part4
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


@[simp]
theorem sctEdgeCutMass_mk (d : ℕ) (beta h : ℝ) (n : ℕ)
    (x y : sctBox d n) :
    sctEdgeCutMass d beta h n s(x, y) =
      sctOrientedCutMass d beta h n x y +
        sctOrientedCutMass d beta h n y x := rfl


theorem sctOrientedCutMass_to_origin_zero {d n : ℕ} (beta h : ℝ)
    (x : sctBox d n) :
    sctOrientedCutMass d beta h n x (sctBoxOrigin d n) = 0 := by
  unfold sctOrientedCutMass
  apply Finset.sum_eq_zero
  intro T _
  by_cases ho : sctBoxOrigin d n ∈ T <;> simp [ho]


theorem sct_bondDelta_bound {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) (e : Sym2 (sctBox d n))
    (he : e ∈ (sctBoxGraph d n).edgeFinset) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      (sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
          (sctBoxOrigin d n) e) ≥
      sctLatticeC d beta h n * sctEdgeCutMass d beta h n e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hadj : (sctBoxGraph d n).Adj x y := by
        simpa using (SimpleGraph.mem_edgeFinset.mp he)
      have hxy : x ≠ y := (sctBoxGraph d n).ne_of_adj hadj
      by_cases hox : sctBoxOrigin d n = x
      · subst x
        rw [sctEdgeCutMass_mk, sctOrientedCutMass_to_origin_zero, add_zero]
        exact sct_incidentBondDelta_bound beta h hbeta hh y hxy
      · by_cases hoy : sctBoxOrigin d n = y
        · subst y
          rw [sctEdgeCutMass_mk, sctOrientedCutMass_to_origin_zero, zero_add]
          rw [Sym2.eq_swap]
          exact sct_incidentBondDelta_bound beta h hbeta hh x hxy.symm
        · exact sct_nonincidentBondDelta_bound beta h hbeta hh hox hoy hxy


theorem sct_sum_bondDelta_bound {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      (sctOriginMag d beta h n *
        ∑ e ∈ (sctBoxGraph d n).edgeFinset,
          HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
            (sctBoxOrigin d n) e) ≥
      sctLatticeC d beta h n *
        ∑ e ∈ (sctBoxGraph d n).edgeFinset,
          sctEdgeCutMass d beta h n e := by
  have hs :
      (∑ e ∈ (sctBoxGraph d n).edgeFinset,
        sctLatticeC d beta h n * sctEdgeCutMass d beta h n e) ≤
      ∑ e ∈ (sctBoxGraph d n).edgeFinset,
        (currentSum (withGhost (sctBoxGraph d n)) beta
            (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
          (sctOriginMag d beta h n *
            HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
              (sctBoxOrigin d n) e) := by
    apply Finset.sum_le_sum
    intro e he
    exact sct_bondDelta_bound (d := d) (n := n) beta h hbeta hh e he
  calc
    sctLatticeC d beta h n *
        ∑ e ∈ (sctBoxGraph d n).edgeFinset,
          sctEdgeCutMass d beta h n e =
      ∑ e ∈ (sctBoxGraph d n).edgeFinset,
        sctLatticeC d beta h n * sctEdgeCutMass d beta h n e := by
          rw [Finset.mul_sum]
    _ ≤ ∑ e ∈ (sctBoxGraph d n).edgeFinset,
        (currentSum (withGhost (sctBoxGraph d n)) beta
            (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
          (sctOriginMag d beta h n *
            HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
              (sctBoxOrigin d n) e) := hs
    _ = (currentSum (withGhost (sctBoxGraph d n)) beta
          (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
        (sctOriginMag d beta h n *
          ∑ e ∈ (sctBoxGraph d n).edgeFinset,
            HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
              (sctBoxOrigin d n) e) := by
      rw [Finset.mul_sum, Finset.mul_sum]


end Sharpness
end StatMech
