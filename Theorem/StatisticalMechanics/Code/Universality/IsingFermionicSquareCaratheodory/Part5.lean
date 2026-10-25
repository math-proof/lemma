/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part4


namespace StatMech.Universality

open Filter Set Topology Metric

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingExpandingSquareRadialSupport_nonempty (k : Nat) :
    (fkIsingExpandingSquareRadialSupport k).Nonempty := by
  classical
  by_cases hk : k = 0
  · simp [fkIsingExpandingSquareRadialSupport, hk]
  · simp [fkIsingExpandingSquareRadialSupport, hk]


theorem fkIsingExpandingSquareRadialSupport_mem_closedBall
    (k : Nat) (a : fkIsingExpandingSquareCaratheodoryApproximation.M k)
    (hk : k ≠ 0)
    (ha : a ∈ fkIsingExpandingSquareRadialSupport k) :
    dist (fkIsingExpandingSquareCaratheodoryApproximation.medialEmbedding k a)
      0 ≤ 4 := by
  classical
  let n := fkIsingExpandingSquareSide k
  let m := k + 1
  let R := k / 2
  have hm : m ≤ n := by simp [m, n, fkIsingExpandingSquareSide]; nlinarith
  have hm2 : 2 ≤ m := by simp [m]; omega
  have hfit : 0 + R + 1 < m := by simp [R, m]; omega
  rw [fkIsingExpandingSquareRadialSupport] at ha
  simp only [hk, ↓reduceDIte] at ha
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_map.mp ha
  have hbase := fkIsingSquareRadialPatchWindowCarrier_scaledPosition_norm_le
    n m 0 0 R hm hm2 hfit hfit p
  have hnear := fkIsingSquareWiredPerturbedCarrierPosition_dist_lt
    n (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
    (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p)
  change dist (fkIsingSquareWiredPerturbedCarrierPosition
      n (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
      (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p)) 0 ≤ 4
  rw [dist_zero_right]
  apply le_of_lt
  calc
      ‖fkIsingSquareWiredPerturbedCarrierPosition
          n (fkIsingExpandingSquareSide_pos k)
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
          (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p)‖ ≤
        ‖((fkIsingExpandingSquareScale k : Real) : Complex) *
          fkIsingSquareWiredCarrierPosition n (fkIsingExpandingSquareSide_pos k)
            (fkIsingSquareRadialPatchWindowCarrier
              n m 0 0 R hm hfit hfit p)‖ +
          dist (fkIsingSquareWiredPerturbedCarrierPosition
            n (fkIsingExpandingSquareSide_pos k)
            (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
            (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p))
            (((fkIsingExpandingSquareScale k : Real) : Complex) *
              fkIsingSquareWiredCarrierPosition n
                (fkIsingExpandingSquareSide_pos k)
                (fkIsingSquareRadialPatchWindowCarrier
                  n m 0 0 R hm hfit hfit p)) := by
        simpa [dist_eq_norm] using
          (norm_le_norm_add_norm_sub'
            (fkIsingSquareWiredPerturbedCarrierPosition
              n (fkIsingExpandingSquareSide_pos k)
              (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
              (fkIsingSquareRadialPatchWindowCarrier n m 0 0 R hm hfit hfit p))
            (((fkIsingExpandingSquareScale k : Real) : Complex) *
              fkIsingSquareWiredCarrierPosition n
                (fkIsingExpandingSquareSide_pos k)
                (fkIsingSquareRadialPatchWindowCarrier
                  n m 0 0 R hm hfit hfit p)))
      _ < 3 + fkIsingExpandingSquareScale k / 10 :=
        add_lt_add_of_le_of_lt (by simpa [m, fkIsingExpandingSquareScale] using hbase)
          hnear
      _ < 4 := by
        have hs : fkIsingExpandingSquareScale k ≤ 1 := by
          rw [fkIsingExpandingSquareScale]
          rw [one_div]
          apply inv_le_one_of_one_le₀
          norm_num
        linarith


theorem fkIsingExpandingSquareRadialSupport_hasEventualCompactWindowDiameter :
    FKIsingCaratheodoryApproximation.HasEventualCompactWindowDiameter
      fkIsingExpandingSquareCaratheodoryApproximation
      fkIsingExpandingSquareRadialSupport := by
  apply FKIsingCaratheodoryApproximation.hasEventualCompactWindowDiameter_of_commonBall
  intro K hK _hKU
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : Complex)
  let B := max 4 (C + 4)
  refine ⟨0, B, (show (0 : Real) ≤ 4 by norm_num).trans
    (le_max_left 4 (C + 4)), ?_⟩
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : k ≠ 0 := by omega
  have hscale : fkIsingExpandingSquareScale k ≤ 1 := by
    rw [fkIsingExpandingSquareScale, one_div]
    apply inv_le_one_of_one_le₀
    norm_num
  have hmesh : fkIsingExpandingSquareMesh k ≤ 4 := by
    rw [fkIsingExpandingSquareMesh]
    nlinarith
  constructor
  · intro a ha
    exact (fkIsingExpandingSquareRadialSupport_mem_closedBall k a hk0 ha).trans
      (le_max_left 4 (C + 4))
  · intro e he
    obtain ⟨z, hzK, hznear⟩ := he
    have hzC : dist z 0 ≤ C := hC hzK
    calc
      dist (fkIsingExpandingSquareCaratheodoryApproximation.medialEmbedding k e)
          0 ≤
        dist (fkIsingExpandingSquareCaratheodoryApproximation.medialEmbedding k e)
            z + dist z 0 := dist_triangle _ _ _
      _ ≤ fkIsingExpandingSquareMesh k + C :=
        add_le_add (by simpa [dist_comm] using hznear) hzC
      _ ≤ 4 + C := by simpa [add_comm] using add_le_add_right hmesh C
      _ = C + 4 := by ring
      _ ≤ B := le_max_right 4 (C + 4)

end
end StatMech.Universality
