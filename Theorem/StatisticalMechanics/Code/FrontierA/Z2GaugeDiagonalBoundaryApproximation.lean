/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDiagonalBoundaryApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
open Filter Topology


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInfiniteVolumeWilsonFreeEnergy_le_paddedDisorderFreeEnergy
    {K : Real} (hK : 0 < K) {a b lx rx ly ry lz rz : Nat}
    (ha : 0 < a) (hb : 0 < b) (hz : 0 < lz + rz) :
    cubicalInfiniteVolumeWilsonFreeEnergy K a b <=
      cubicalPaddedDisorderFreeEnergy K a b lx rx ly ry lz rz := by
  have hpadded := cubicalPaddedWilsonExpectation_pos hK
    a b lx rx ly ry lz rz
  have horder := cubicalPaddedWilsonExpectation_le_infiniteVolume hK
    a b lx rx ly ry lz rz
  have hlog := Real.log_le_log hpadded horder
  calc
    cubicalInfiniteVolumeWilsonFreeEnergy K a b <=
        -Real.log (cubicalPaddedWilsonExpectation K a b lx rx ly ry lz rz) := by
      unfold cubicalInfiniteVolumeWilsonFreeEnergy
      exact neg_le_neg hlog
    _ = cubicalPaddedDisorderFreeEnergy K a b lx rx ly ry lz rz := by
      simpa [cubicalPaddedDisorderFreeEnergy] using
        (neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy
          hK ha hb hz)


theorem exists_cubicalPaddedDisorderDensity_close_infiniteVolume
    {K : Real} (hK : 0 < K) (n : Nat) {eps : Real} (heps : 0 < eps) :
    exists m : Nat, 0 < m /\
      0 <=
        cubicalPaddedDisorderFreeEnergy K
              (centralSquareSide n) (centralSquareSide n) m m m m m m /
            ((centralSquareSide n : Nat) : Real) ^ 2 -
          cubicalInfiniteVolumeSquareWilsonDensity K n /\
      cubicalPaddedDisorderFreeEnergy K
              (centralSquareSide n) (centralSquareSide n) m m m m m m /
            ((centralSquareSide n : Nat) : Real) ^ 2 -
          cubicalInfiniteVolumeSquareWilsonDensity K n < eps := by
  let side : Nat := centralSquareSide n
  have hside : 0 < side := by simp [side, centralSquareSide]
  have harea : (0 : Real) < ((side : Real) ^ 2) := by positivity
  have hlim : Tendsto
      (fun m : Nat => cubicalPaddedDisorderFreeEnergy K
        side side m m m m m m) atTop
      (nhds (cubicalInfiniteVolumeWilsonFreeEnergy K side side)) :=
    cubicalPaddedDisorderFreeEnergy_tendsto_infiniteVolume
      hK hside hside (fun m => m) (fun m => m) (fun m => m)
        (fun m => m) (fun m => m) (fun m => m)
        tendsto_id tendsto_id tendsto_id tendsto_id tendsto_id tendsto_id
  have hclose : ∀ᶠ m : Nat in atTop,
      cubicalPaddedDisorderFreeEnergy K side side m m m m m m <
        cubicalInfiniteVolumeWilsonFreeEnergy K side side +
          eps * ((side : Real) ^ 2) :=
    hlim.eventually (Iio_mem_nhds (lt_add_of_pos_right _ (mul_pos heps harea)))
  have hall := hclose.and (eventually_ge_atTop 1)
  obtain ⟨m, hmclose, hm⟩ := hall.exists
  have hmpos : 0 < m := by omega
  have hfree :=
    cubicalInfiniteVolumeWilsonFreeEnergy_le_paddedDisorderFreeEnergy
      (a := side) (b := side) (lx := m) (rx := m) (ly := m) (ry := m)
      (lz := m) (rz := m) hK hside hside (by omega : 0 < m + m)
  refine ⟨m, hmpos, ?_, ?_⟩
  · change 0 <=
      cubicalPaddedDisorderFreeEnergy K side side m m m m m m /
          ((side : Real) ^ 2) -
        cubicalInfiniteVolumeWilsonFreeEnergy K side side /
          ((side : Real) ^ 2)
    rw [sub_nonneg]
    exact div_le_div_of_nonneg_right hfree harea.le
  · change
      cubicalPaddedDisorderFreeEnergy K side side m m m m m m /
          ((side : Real) ^ 2) -
        cubicalInfiniteVolumeWilsonFreeEnergy K side side /
          ((side : Real) ^ 2) < eps
    rw [← sub_div]
    rw [div_lt_iff₀ harea]
    linarith


end
end StatMech.FrontierA
