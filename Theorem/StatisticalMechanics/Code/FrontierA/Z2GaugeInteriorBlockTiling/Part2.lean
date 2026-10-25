/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling.Part2
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInteriorBlockTileLoop_eq_boundary
    (L p k : Nat) (q : Fin k × Fin k) :
    cubicalInteriorBlockTileLoop L p k q =
      gaugeSurfaceBoundary cubicalPlaquetteIncidence
        (cubicalInteriorBlockTileSheet L p k q) := by
  unfold cubicalInteriorBlockTileLoop cubicalInteriorBlockTileSheet
    cubicalXYLoop
  exact (gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
    cubicalPlaquetteIncidence
    (cubicalEdgeChart (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]))
    (cubicalPlaquetteChart (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]))
    (fun plaquette => cubicalPlaquetteIncidence_chart
      (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]) plaquette)
    (cubicalXYSheet (a := L) (b := L) (c := 0) (0 : Fin 1))).symm

theorem cubicalInteriorBlockTileSheet_pairwise_disjoint
    (L p k : Nat) (hL : 0 < L) :
    ∀ q : Fin k × Fin k, q ∈ (Finset.univ : Finset (Fin k × Fin k)) ->
      ∀ r : Fin k × Fin k, r ∈ (Finset.univ : Finset (Fin k × Fin k)) ->
        q ≠ r -> Disjoint (cubicalInteriorBlockTileSheet L p k q)
          (cubicalInteriorBlockTileSheet L p k r) := by
  intro q _ r _ hqr
  rw [Finset.disjoint_left]
  intro plaquette hpq hpr
  cases plaquette with
  | xy x y z =>
      simp only [cubicalInteriorBlockTileSheet, cubicalXYSheet,
        Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hpq hpr
      obtain ⟨_, ⟨ijq, _, rfl⟩, hpq⟩ := hpq
      obtain ⟨_, ⟨ijr, _, rfl⟩, hpr⟩ := hpr
      change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy x y z at hpq hpr
      rw [CubicalPlaquette.xy.injEq] at hpq hpr
      have hx : q.1.val = r.1.val := by
        have h := congrArg Fin.val (hpq.1.trans hpr.1.symm)
        simp only [finOffsetEmbedding_val] at h
        have h' : q.1.val * L + ijq.1.val =
            r.1.val * L + ijr.1.val := by omega
        have hd := congrArg (fun z : Nat => z / L) h'
        simpa [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_div hL,
          Nat.div_eq_of_lt ijq.1.isLt,
          Nat.div_eq_of_lt ijr.1.isLt] using hd
      have hy : q.2.val = r.2.val := by
        have h := congrArg Fin.val (hpq.2.1.trans hpr.2.1.symm)
        simp only [finOffsetEmbedding_val] at h
        have h' : q.2.val * L + ijq.2.val =
            r.2.val * L + ijr.2.val := by omega
        have hd := congrArg (fun z : Nat => z / L) h'
        simpa [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_div hL,
          Nat.div_eq_of_lt ijq.2.isLt,
          Nat.div_eq_of_lt ijr.2.isLt] using hd
      apply hqr
      apply Prod.ext <;> apply Fin.ext
      · exact hx
      · exact hy
  | xz x y z =>
      simp [cubicalInteriorBlockTileSheet, cubicalXYSheet,
        cubicalPlaquetteChart] at hpq
  | yz x y z =>
      simp [cubicalInteriorBlockTileSheet, cubicalXYSheet,
        cubicalPlaquetteChart] at hpq

end
end StatMech.FrontierA
