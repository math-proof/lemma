/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4
import Mathlib.Analysis.Real.Pi.Wallis
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore.Part2


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem tendsto_sixVertexIdealWallisLogCorrection :
    Tendsto sixVertexIdealWallisLogCorrection atTop
      (nhds (-Real.log (Real.pi / 2))) := by
  unfold sixVertexIdealWallisLogCorrection
  exact ((Real.continuousAt_log (ne_of_gt Real.pi_div_two_pos)).tendsto.comp
    Real.Wallis.tendsto_W_nhds_pi_div_two).neg

theorem sixVertexIdealWallisLogCorrection_eq_sum (n : Nat) :
    sixVertexIdealWallisLogCorrection n =
      ∑ j ∈ Finset.range n,
        Real.log (((2 * (j : Real) + 1) * (2 * j + 3)) /
          (2 * j + 2) ^ 2) := by
  have hodd1 (j : Nat) : (2 * (j : Real) + 1) ≠ 0 := by positivity
  have hodd3 (j : Nat) : (2 * (j : Real) + 3) ≠ 0 := by positivity
  have heven (j : Nat) : (2 * (j : Real) + 2) ≠ 0 := by positivity
  have hfactor (j : Nat) :
      Real.log (((2 * (j : Real) + 1) * (2 * j + 3)) /
          (2 * j + 2) ^ 2) =
        -Real.log (((2 * (j : Real) + 2) / (2 * j + 1)) *
          ((2 * j + 2) / (2 * j + 3))) := by
    rw [Real.log_div (mul_ne_zero (hodd1 j) (hodd3 j))
      (pow_ne_zero 2 (heven j)), Real.log_mul (hodd1 j) (hodd3 j),
      Real.log_pow, Real.log_mul
        (div_ne_zero (heven j) (hodd1 j))
        (div_ne_zero (heven j) (hodd3 j)),
      Real.log_div (heven j) (hodd1 j),
      Real.log_div (heven j) (hodd3 j)]
    ring
  unfold sixVertexIdealWallisLogCorrection Real.Wallis.W
  rw [Real.log_prod (fun j hj => mul_ne_zero
    (div_ne_zero (heven j) (hodd1 j))
    (div_ne_zero (heven j) (hodd3 j)))]
  simp_rw [hfactor]
  rw [Finset.sum_neg_distrib]


theorem two_sum_midpoint_sub_eq_endpoint_add_secondDifference
    (n : Nat) (x : Nat -> Real) (f : Real -> Real) :
    2 * ∑ j ∈ Finset.range n,
        (f ((x j + x (j + 1)) / 2) - f (x j)) =
      f (x n) - f (x 0) +
        ∑ j ∈ Finset.range n,
          (2 * f ((x j + x (j + 1)) / 2) - f (x j) - f (x (j + 1))) := by
  rw [show f (x n) - f (x 0) =
    ∑ j ∈ Finset.range n, (f (x (j + 1)) - f (x j)) by
      rw [Finset.sum_sub_distrib]
      have h := Finset.sum_range_sub' (fun j => f (x j)) n
      rw [Finset.sum_sub_distrib] at h
      linarith]
  rw [<- Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end StatMech.FrontierD
