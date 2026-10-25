/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part2


namespace StatMech.Universality

open Filter Set Topology Metric

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingExpandingSquare_compact_eventually_mem
    (K : Set Complex) (hK : IsCompact K) :
    ∀ᶠ k in atTop, K ⊆ fkIsingExpandingSquareCarrier k := by
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : Complex)
  obtain ⟨N : Nat, hN⟩ := exists_nat_gt (max C 0 + 2)
  filter_upwards [eventually_ge_atTop N] with k hk
  intro z hz
  have hzC : dist z 0 ≤ C := by
    simpa [dist_comm] using hC hz
  have hCnonneg : 0 ≤ C := by
    have hdist : 0 ≤ dist z 0 := dist_nonneg
    linarith
  have hzNorm : ‖z‖ ≤ C := by simpa [dist_eq_norm] using hzC
  have hzre : |z.re| ≤ C := (Complex.abs_re_le_norm z).trans hzNorm
  have hzim : |z.im| ≤ C := (Complex.abs_im_le_norm z).trans hzNorm
  let side := fkIsingExpandingSquareSide k
  let scale := fkIsingExpandingSquareScale k
  have hscale : 0 < scale := fkIsingExpandingSquareScale_pos k
  have hklarge : C + 1 < (k + 1 : Nat) := by
    have hkreal : (N : Real) ≤ (k : Real) := by exact_mod_cast hk
    have hCmax : C ≤ max C 0 := le_max_left C 0
    push_cast
    linarith
  have hx0 : -(side : Int) ≤ ⌊z.re / scale⌋ := by
    rw [Int.le_floor]
    have hre := (abs_le.mp hzre).1
    simp [side, scale, fkIsingExpandingSquareSide,
      fkIsingExpandingSquareScale]
    field_simp
    norm_num [Nat.cast_add] at hklarge ⊢
    nlinarith
  have hx1 : ⌊z.re / scale⌋ < (side : Int) := by
    rw [Int.floor_lt]
    have hre := (abs_le.mp hzre).2
    simp [side, scale, fkIsingExpandingSquareSide,
      fkIsingExpandingSquareScale]
    field_simp
    norm_num [Nat.cast_add] at hklarge ⊢
    nlinarith
  have hy0 : -(side : Int) ≤ ⌊z.im / scale⌋ := by
    rw [Int.le_floor]
    have him := (abs_le.mp hzim).1
    simp [side, scale, fkIsingExpandingSquareSide,
      fkIsingExpandingSquareScale]
    field_simp
    norm_num [Nat.cast_add] at hklarge ⊢
    nlinarith
  have hy1 : ⌊z.im / scale⌋ ≤ (side : Int) := by
    have hylt : ⌊z.im / scale⌋ < (side : Int) := by
      rw [Int.floor_lt]
      have him := (abs_le.mp hzim).2
      simp [side, scale, fkIsingExpandingSquareSide,
        fkIsingExpandingSquareScale]
      field_simp
      norm_num [Nat.cast_add] at hklarge ⊢
      nlinarith
    omega
  obtain ⟨a, ha⟩ := exists_fkIsingSquareWiredCarrier_scaledPosition_near
    side (fkIsingExpandingSquareSide_pos k) scale hscale z hx0 hx1 hy0 hy1
  have hpert := fkIsingSquareWiredPerturbedCarrierPosition_dist_lt
    side (fkIsingExpandingSquareSide_pos k) scale hscale a
  refine ⟨a, ?_⟩
  change dist z (fkIsingSquareWiredPerturbedCarrierPosition
      side (fkIsingExpandingSquareSide_pos k) scale hscale a) ≤ _
  apply le_of_lt
  calc
    dist z (fkIsingSquareWiredPerturbedCarrierPosition
        side (fkIsingExpandingSquareSide_pos k) scale hscale a) ≤
      dist z ((scale : Complex) *
          fkIsingSquareWiredCarrierPosition
            side (fkIsingExpandingSquareSide_pos k) a) +
        dist ((scale : Complex) *
          fkIsingSquareWiredCarrierPosition
            side (fkIsingExpandingSquareSide_pos k) a)
          (fkIsingSquareWiredPerturbedCarrierPosition
            side (fkIsingExpandingSquareSide_pos k) scale hscale a) :=
      dist_triangle _ _ _
    _ < 3 * scale + scale / 10 :=
      add_lt_add ha (by simpa [dist_comm] using hpert)
    _ ≤ fkIsingExpandingSquareMesh k := by
      simp [fkIsingExpandingSquareMesh, scale]
      linarith


end
end StatMech.Universality
