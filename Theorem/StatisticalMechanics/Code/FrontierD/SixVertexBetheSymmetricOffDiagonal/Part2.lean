/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricCovering
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N m : Nat} (hm : 0 < m) (hN : 0 < N) (hhalf : N = 2 * (m + m))
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q)) (j : Fin m) :
    |(∑ k ∈ Finset.univ.erase j,
          sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) -
        ∫ y in -q ⟨m - 1, by
              omega⟩..q ⟨0, hm⟩,
          sixVertexSymmetricScatteringDerivative c (-q j) y| ≤
      sixVertexSymmetricTailJacobianOffDiagonalError c N := by
  let mesh := 1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)
  let H := sixVertexSymmetricScatteringDerivative c (-q j)
  let L := (sixVertexSymmetricScatteringLipschitzConstant c : Real)
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hgap (k : Fin m) : 0 ≤ sixVertexPositiveHalfRootGap q k :=
    (sixVertexPositiveHalfRootGap_pos_of_open hopen k).le
  have hmesh (k : Fin m) : sixVertexPositiveHalfRootGap q k ≤ mesh :=
    sixVertexPositiveHalfRootGap_upper_tail hc htail hN hhalf hopen hsol k
  have hquad := abs_positiveHalfScatteringEndpointSum_sub_integral_le
    hc hm hopen hmesh j
  have hterm (k : Fin m) :
      |sixVertexPositiveHalfRootGap q k * H (-q k)| ≤ 2 * R * mesh := by
    rw [abs_mul, abs_of_nonneg (hgap k)]
    have hH := abs_sixVertexSymmetricScatteringDerivative_le hc (-q j) (-q k)
    have hR : 0 ≤ 2 * R := by
      have hd := one_lt_sixVertexAnisotropyMagnitude hc
      exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by linarith))
    calc
      sixVertexPositiveHalfRootGap q k * |H (-q k)| ≤
          sixVertexPositiveHalfRootGap q k * (2 * R) :=
        mul_le_mul_of_nonneg_left hH (hgap k)
      _ ≤ mesh * (2 * R) := mul_le_mul_of_nonneg_right (hmesh k) hR
      _ = 2 * R * mesh := by ring
  have hoffEq :
      (∑ k ∈ Finset.univ.erase j,
          sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) =
        ∑ k ∈ Finset.univ.erase j,
          sixVertexPositiveHalfRootGap q k * H (-q k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : j ≠ k := Ne.symm (Finset.mem_erase.mp hk).1
    rw [sixVertexBethePositiveHalfScaledJacobianMatrix,
      sixVertexBethePositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative hkj]
    ring
  let I := ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩, H y
  have herase :
      (∑ k ∈ Finset.univ.erase j,
          sixVertexPositiveHalfRootGap q k * H (-q k)) =
        (∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
          sixVertexPositiveHalfRootGap q j * H (-q j) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    ring
  change _ ≤ sixVertexSymmetricTailJacobianOffDiagonalError c N
  rw [hoffEq, herase]
  unfold sixVertexSymmetricTailJacobianOffDiagonalError
  change |((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
      sixVertexPositiveHalfRootGap q j * H (-q j)) - I| ≤
        ((2 * Real.pi) * L + 2 * R) * mesh
  calc
    |((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
        sixVertexPositiveHalfRootGap q j * H (-q j)) - I| ≤
      |(∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) - I| +
        |sixVertexPositiveHalfRootGap q j * H (-q j)| := by
      rw [show ((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
          sixVertexPositiveHalfRootGap q j * H (-q j)) - I =
        ((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) - I) -
          sixVertexPositiveHalfRootGap q j * H (-q j) by ring]
      exact abs_sub _ _
    _ ≤ L * mesh * (2 * Real.pi) + 2 * R * mesh :=
      add_le_add hquad (hterm j)
    _ = ((2 * Real.pi) * L + 2 * R) * mesh := by ring

end
end StatMech.FrontierD
