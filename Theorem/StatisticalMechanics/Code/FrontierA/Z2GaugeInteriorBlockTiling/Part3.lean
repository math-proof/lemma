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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling.Part3
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInteriorBlockCentralLoop_eq_boundary
    (L p k : Nat) :
    cubicalInteriorBlockCentralLoop L p k =
      gaugeSurfaceBoundary cubicalPlaquetteIncidence
        (cubicalInteriorBlockCentralSheet L p k) := by
  unfold cubicalInteriorBlockCentralLoop cubicalInteriorBlockCentralSheet
    cubicalXYLoop
  exact (gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
    cubicalPlaquetteIncidence
    (cubicalEdgeChart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]))
    (cubicalPlaquetteChart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]))
    (fun plaquette => cubicalPlaquetteIncidence_chart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]) plaquette)
    (cubicalXYSheet (a := k * L) (b := k * L) (c := 0)
      (0 : Fin 1))).symm

theorem cubicalInteriorBlockTileSheet_biUnion
    (L p k : Nat) (hL : 0 < L) :
    (Finset.univ : Finset (Fin k × Fin k)).biUnion
        (cubicalInteriorBlockTileSheet L p k) =
      cubicalInteriorBlockCentralSheet L p k := by
  ext plaquette
  cases plaquette with
  | xy x y z =>
      constructor
      · intro hp
        simp only [Finset.mem_biUnion] at hp
        obtain ⟨q, _, hq⟩ := hp
        simp only [cubicalInteriorBlockTileSheet, cubicalXYSheet,
          Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hq
        obtain ⟨_, ⟨ij, _, rfl⟩, hpq⟩ := hq
        simp only [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
          Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and]
        let ci : Fin (k * L) := ⟨q.1.val * L + ij.1.val, by
          have hq' : q.1.val + 1 <= k := Nat.succ_le_iff.mpr q.1.isLt
          have hmul := Nat.mul_le_mul_right L hq'
          calc
            q.1.val * L + ij.1.val < q.1.val * L + L :=
              Nat.add_lt_add_left ij.1.isLt _
            _ = (q.1.val + 1) * L := by ring
            _ <= k * L := hmul⟩
        let cj : Fin (k * L) := ⟨q.2.val * L + ij.2.val, by
          have hq' : q.2.val + 1 <= k := Nat.succ_le_iff.mpr q.2.isLt
          have hmul := Nat.mul_le_mul_right L hq'
          calc
            q.2.val * L + ij.2.val < q.2.val * L + L :=
              Nat.add_lt_add_left ij.2.isLt _
            _ = (q.2.val + 1) * L := by ring
            _ <= k * L := hmul⟩
        refine ⟨CubicalPlaquette.xy ci cj (0 : Fin 1), ?_, ?_⟩
        · exact ⟨(ci, cj), rfl⟩
        · change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy x y z
          have hpqcoord := CubicalPlaquette.xy.inj hpq
          rw [CubicalPlaquette.xy.injEq]
          constructor
          · apply Fin.ext
            calc
              (finOffsetEmbedding p (by simp [cubicalInteriorBlockSide]) ci).val =
                  p + (q.1.val * L + ij.1.val) := by rfl
              _ = (finOffsetEmbedding (p + q.1.val * L)
                  (cubicalInteriorBlockTile_fit L p k q.1) ij.1).val := by
                    simp only [finOffsetEmbedding_val]
                    omega
              _ = x.val := congrArg Fin.val hpqcoord.1
          constructor
          · apply Fin.ext
            calc
              (finOffsetEmbedding p (by simp [cubicalInteriorBlockSide]) cj).val =
                  p + (q.2.val * L + ij.2.val) := by rfl
              _ = (finOffsetEmbedding (p + q.2.val * L)
                  (cubicalInteriorBlockTile_fit L p k q.2) ij.2).val := by
                    simp only [finOffsetEmbedding_val]
                    omega
              _ = y.val := congrArg Fin.val hpqcoord.2.1
          · exact hpqcoord.2.2
      · intro hp
        simp only [cubicalInteriorBlockCentralSheet, cubicalXYSheet,
          Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and] at hp
        obtain ⟨_, ⟨ij, _, rfl⟩, hp⟩ := hp
        have hpcoord := CubicalPlaquette.xy.inj hp
        let qx : Fin k := ⟨ij.1.val / L, by
          apply (Nat.div_lt_iff_lt_mul hL).2
          simpa [Nat.mul_comm] using ij.1.isLt⟩
        let qy : Fin k := ⟨ij.2.val / L, by
          apply (Nat.div_lt_iff_lt_mul hL).2
          simpa [Nat.mul_comm] using ij.2.isLt⟩
        let ix : Fin L := ⟨ij.1.val % L, Nat.mod_lt _ hL⟩
        let iy : Fin L := ⟨ij.2.val % L, Nat.mod_lt _ hL⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨(qx, qy), Finset.mem_univ _, ?_⟩
        apply Finset.mem_map.mpr
        refine ⟨CubicalPlaquette.xy ix iy (0 : Fin 1), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨(ix, iy), Finset.mem_univ _, rfl⟩
        · change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy _ _ _
          rw [CubicalPlaquette.xy.injEq]
          constructor
          · apply Fin.ext
            simp only [finOffsetEmbedding_val]
            calc
              p + qx.val * L + ix.val = p + ij.1.val := by
                rw [show qx.val = ij.1.val / L by rfl,
                  show ix.val = ij.1.val % L by rfl]
                have hinner : (ij.1.val / L) * L + ij.1.val % L =
                    ij.1.val := by
                  simpa [Nat.mul_comm] using Nat.div_add_mod ij.1.val L
                omega
              _ = x.val := congrArg Fin.val hpcoord.1
          constructor
          · apply Fin.ext
            simp only [finOffsetEmbedding_val]
            calc
              p + qy.val * L + iy.val = p + ij.2.val := by
                rw [show qy.val = ij.2.val / L by rfl,
                  show iy.val = ij.2.val % L by rfl]
                have hinner : (ij.2.val / L) * L + ij.2.val % L =
                    ij.2.val := by
                  simpa [Nat.mul_comm] using Nat.div_add_mod ij.2.val L
                omega
              _ = y.val := congrArg Fin.val hpcoord.2.1
          · apply Fin.ext
            exact congrArg Fin.val hpcoord.2.2
  | xz x y z =>
      simp [cubicalInteriorBlockTileSheet,
        cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        cubicalPlaquetteChart]
  | yz x y z =>
      simp [cubicalInteriorBlockTileSheet,
        cubicalInteriorBlockCentralSheet, cubicalXYSheet,
        cubicalPlaquetteChart]


theorem cubicalPaddedWilsonExpectation_pow_sq_le_interiorBlockCentral
    {K : Real} (hK : 0 < K) (L p k : Nat) (hL : 0 < L) :
    (cubicalPaddedWilsonExpectation K L L p p p p p p) ^ (k * k) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k) => K)
        (cubicalInteriorBlockCentralLoop L p k) := by
  let N := cubicalInteriorBlockSide L p k
  let smallW := cubicalPaddedWilsonExpectation K L L p p p p p p
  let tileW : Fin k × Fin k -> Real := fun q =>
    gaugeWilsonExpectation cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette N N N => K)
      (cubicalInteriorBlockTileLoop L p k q)
  have htile (q : Fin k × Fin k) : smallW <= tileW q := by
    let A := p + L + p
    let C := p + p
    let L0 := cubicalXYLoop (a := L) (b := L) (c := 0) (0 : Fin 1)
    let inner := cubicalEdgeChart p p p
      (a := L) (b := L) (c := 0) (A := A) (B := A) (C := C)
      (by dsimp [A]; omega) (by dsimp [A]; omega) (by dsimp [C]; omega)
    have hxOuter : q.1.val * L + A <= N := by
      have hq : q.1.val + 1 <= k := Nat.succ_le_iff.mpr q.1.isLt
      have hmul := Nat.mul_le_mul_right L hq
      dsimp [A, N, cubicalInteriorBlockSide]
      nlinarith
    have hyOuter : q.2.val * L + A <= N := by
      have hq : q.2.val + 1 <= k := Nat.succ_le_iff.mpr q.2.isLt
      have hmul := Nat.mul_le_mul_right L hq
      dsimp [A, N, cubicalInteriorBlockSide]
      nlinarith
    have hzOuter : 0 + C <= N := by
      dsimp [C, N, cubicalInteriorBlockSide]
      omega
    let outer := cubicalEdgeChart (q.1.val * L) (q.2.val * L) 0
      (a := A) (b := A) (c := C) (A := N) (B := N) (C := N)
      hxOuter hyOuter hzOuter
    let target := cubicalEdgeChart (p + q.1.val * L)
      (p + q.2.val * L) p
      (a := L) (b := L) (c := 0) (A := N) (B := N) (C := N)
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by dsimp [N, cubicalInteriorBlockSide]; omega)
    have hmap : (L0.map inner).map outer = L0.map target := by
      rw [Finset.map_map]
      congr 1
      ext edge
      simpa [inner, outer, target, A, C, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using
        (cubicalEdgeChart_comp_apply p p p
          (q.1.val * L) (q.2.val * L) 0
          (by dsimp [A]; omega) (by dsimp [A]; omega)
          (by dsimp [C]; omega) hxOuter hyOuter hzOuter edge)
    have h := cubicalWilsonExpectation_le_chart
      (a := A) (b := A) (c := C) (A := N) (B := N) (C := N)
      (q.1.val * L) (q.2.val * L) 0 hxOuter hyOuter hzOuter hK.le
      (L0.map inner)
    rw [hmap] at h
    simpa [smallW, tileW, cubicalPaddedWilsonExpectation,
      cubicalInteriorBlockTileLoop, L0, inner, target, A, C, N] using h
  have hsmall_nonneg : 0 <= smallW :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (p + L + p) (p + L + p) (p + p) => K)
      (fun _ => hK) _).1
  have hprod : smallW ^ (k * k) <=
      ∏ q : Fin k × Fin k, tileW q := by
    have hp := Finset.prod_le_prod
      (s := (Finset.univ : Finset (Fin k × Fin k)))
      (f := fun _ => smallW) (g := tileW)
      (fun _ _ => hsmall_nonneg) (fun q _ => htile q)
    simpa using hp
  have hglue := gaugeWilsonExpectation_prod_boundary_le_biUnion
    cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette N N N => K) (fun _ => hK)
    (Finset.univ : Finset (Fin k × Fin k))
    (cubicalInteriorBlockTileSheet L p k)
    (cubicalInteriorBlockTileSheet_pairwise_disjoint L p k hL)
  dsimp [N] at hglue
  simp_rw [← cubicalInteriorBlockTileLoop_eq_boundary] at hglue
  rw [cubicalInteriorBlockTileSheet_biUnion L p k hL] at hglue
  rw [← cubicalInteriorBlockCentralLoop_eq_boundary] at hglue
  exact hprod.trans (by simpa [smallW, tileW, N] using hglue)


theorem cubicalInteriorBlockCentralDisorderFreeEnergy_le_tiles
    {K : Real} (hK : 0 < K) (L p k : Nat)
    (hL : 0 < L) (hp : 0 < p) (hk : 0 < k) :
    multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k)
          (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K)
        (cubicalInteriorBlockCentralSheet L p k) <=
      (k * k : Nat) *
        cubicalPaddedDisorderFreeEnergy K L L p p p p p p := by
  let N := cubicalInteriorBlockSide L p k
  let Wp := cubicalPaddedWilsonExpectation K L L p p p p p p
  let Wc := gaugeWilsonExpectation cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette N N N => K)
    (cubicalInteriorBlockCentralLoop L p k)
  have hpow : Wp ^ (k * k) <= Wc := by
    simpa [Wp, Wc, N] using
      cubicalPaddedWilsonExpectation_pow_sq_le_interiorBlockCentral
        hK L p k hL
  have hpW : 0 < Wp := cubicalPaddedWilsonExpectation_pos hK
    L L p p p p p p
  have hcW : 0 < Wc := by
    dsimp [Wc]
    rw [cubicalInteriorBlockCentralLoop_eq_boundary]
    apply (gaugeWilsonExpectation_pos_iff_exists_boundary
      cubicalPlaquetteIncidence (fun _ : CubicalPlaquette N N N => K)
      (fun _ => hK) _).2
    exact ⟨cubicalInteriorBlockCentralSheet L p k,
      hasWilsonBoundary_gaugeSurfaceBoundary _ _⟩
  have hlog := Real.log_le_log (pow_pos hpW (k * k)) hpow
  rw [Real.log_pow] at hlog
  have hcentral :=
    neg_log_cubicalWilsonExpectation_eq_disorderFreeEnergy_of_surface
      (A := N) (B := N) (C := N)
      (by dsimp [N, cubicalInteriorBlockSide]; positivity)
      (by dsimp [N, cubicalInteriorBlockSide]; positivity)
      (by dsimp [N, cubicalInteriorBlockSide]; positivity)
      (fun _ : CubicalPlaquette N N N => K) (fun _ => hK)
      (cubicalInteriorBlockCentralSheet L p k)
  have hpadded :=
    neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy
      (a := L) (b := L) (lx := p) (rx := p) (ly := p) (ry := p)
      (lz := p) (rz := p) hK hL hL (by omega)
  change multibondDisorderFreeEnergy cubicalDualEnds
      (fun _ : CubicalPlaquette N N N => gaugeDualCoupling K)
      (cubicalInteriorBlockCentralSheet L p k) <= _
  rw [← hcentral]
  rw [show cubicalPaddedDisorderFreeEnergy K L L p p p p p p =
      -Real.log Wp by
    dsimp [Wp]
    simpa [cubicalPaddedDisorderFreeEnergy] using hpadded.symm]
  dsimp [Wp, Wc] at hlog
  rw [cubicalInteriorBlockCentralLoop_eq_boundary] at hlog
  linarith

end
end StatMech.FrontierA
