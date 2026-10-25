/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricCovering
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexEvenSymmetricBetheRootJacobian_injective_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcount : m + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (m + m)
      (sixVertexEvenSymmetricLift m q) x)
    (hmargin : sixVertexSymmetricScatteringBoundaryBound c +
      2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower <
        2 * Real.pi) :
    Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  let mesh := 1 / ((N : Real) * lower)
  let G : Fin m → Real := fun j =>
    ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩,
      sixVertexSymmetricScatteringDerivative c (-q j) y
  let D := sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower
  let O := sixVertexSymmetricJacobianOffDiagonalErrorOfLower c N lower
  let eps := sixVertexSymmetricJacobianTotalErrorOfLower c N lower
  let M := sixVertexSymmetricScatteringBoundaryBound c
  have hD : 0 ≤ D := by
    dsimp [D, sixVertexSymmetricJacobianDiagonalErrorOfLower]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hO : 0 ≤ O := by
    dsimp [O, sixVertexSymmetricJacobianOffDiagonalErrorOfLower]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have heps : 0 ≤ eps := by
    dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower]
    exact add_nonneg hD hO
  have hM : 0 ≤ M := sixVertexSymmetricScatteringBoundaryBound_nonneg hc
  have hmesh (k : Fin m) : sixVertexPositiveHalfRootGap q k ≤ mesh :=
    sixVertexPositiveHalfRootGap_upper_of_finiteDensityLower
      hc hN hopen hsol hlower hdensity k
  apply sixVertexEvenSymmetricBetheRootJacobian_injective_of_sourceBounds
    hc q hopen G eps M heps hM hmargin
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower
        hc hN hcount hopen hsol hlower hdensity j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower, D, O] at ⊢
      linarith)
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh
        (N := N) hc hm hopen hmesh j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower, O,
        sixVertexSymmetricJacobianOffDiagonalErrorOfLower, mesh] at ⊢
      linarith)
  · intro j
    dsimp [G]
    apply intervalIntegral_sixVertexSymmetricScatteringDerivative_root_bounds
      hc hopen j ⟨0, hm⟩ ⟨m - 1, by omega⟩
    exact (sixVertexEvenSymmetricLift_positive_strictMono hopen).monotone (by
      simp only [Fin.le_def]
      omega)

theorem sixVertexEvenSymmetricBetheRootJacobian_injective_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hhalf : N = 2 * (m + m))
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    (hmargin : sixVertexSymmetricScatteringBoundaryBound c +
      2 * sixVertexSymmetricTailJacobianTotalError c N < 2 * Real.pi) :
    Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  let G : Fin m → Real := fun j =>
    ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩,
      sixVertexSymmetricScatteringDerivative c (-q j) y
  let D := sixVertexSymmetricTailJacobianDiagonalError c N
  let O := sixVertexSymmetricTailJacobianOffDiagonalError c N
  let eps := sixVertexSymmetricTailJacobianTotalError c N
  let M := sixVertexSymmetricScatteringBoundaryBound c
  have hfloor : 0 < sixVertexTailFiniteDensityFloor c :=
    sixVertexTailFiniteDensityFloor_pos hc htail
  have hD : 0 ≤ D := by
    dsimp [D, sixVertexSymmetricTailJacobianDiagonalError]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hO : 0 ≤ O := by
    dsimp [O, sixVertexSymmetricTailJacobianOffDiagonalError]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have heps : 0 ≤ eps := by
    dsimp [eps, sixVertexSymmetricTailJacobianTotalError]
    exact add_nonneg hD hO
  have hM : 0 ≤ M :=
    sixVertexSymmetricScatteringBoundaryBound_nonneg hc
  apply sixVertexEvenSymmetricBetheRootJacobian_injective_of_sourceBounds
    hc q hopen G eps M heps hM hmargin
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_tail
        hc htail hN hhalf hopen hsol j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricTailJacobianTotalError, D, O] at ⊢
      linarith)
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_tail
        hc htail hm hN hhalf hopen hsol j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricTailJacobianTotalError, D, O] at ⊢
      linarith)
  · intro j
    dsimp [G]
    apply intervalIntegral_sixVertexSymmetricScatteringDerivative_root_bounds
      hc hopen j ⟨0, hm⟩ ⟨m - 1, by omega⟩
    exact (sixVertexEvenSymmetricLift_positive_strictMono hopen).monotone (by
      simp only [Fin.le_def]
      omega)

theorem sixVertexSymmetricTailJacobianTotalError_fourWidth_tendsto_zero
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    Tendsto (fun k : Nat => sixVertexSymmetricTailJacobianTotalError c
      (sixVertexFourWidth 0 k)) atTop (nhds 0) := by
  let d := sixVertexAnisotropyMagnitude c
  let floor := sixVertexTailFiniteDensityFloor c
  let L := (sixVertexFiniteRootDensityLipschitzConstant c : Real)
  let S := (sixVertexSymmetricScatteringLipschitzConstant c : Real)
  let R := d / (d - 1)
  let A := Real.pi * L / floor ^ 2 + R / (2 * floor) +
    ((2 * Real.pi) * S + 2 * R) / (4 * floor)
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have h := (tendsto_const_div_atTop_nhds_zero_nat A).comp
    (tendsto_add_atTop_nat 1)
  apply h.congr'
  filter_upwards [] with k
  unfold sixVertexSymmetricTailJacobianTotalError
    sixVertexSymmetricTailJacobianDiagonalError
    sixVertexSymmetricTailJacobianOffDiagonalError sixVertexFourWidth
  dsimp [A, d, floor, L, S, R]
  have hk : (0 : Real) < k + 1 := by positivity
  field_simp [hfloor.ne', hk.ne']
  push_cast
  ring

theorem eventually_sixVertexSymmetricTailJacobian_margin
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexSymmetricScatteringBoundaryBound c +
        2 * sixVertexSymmetricTailJacobianTotalError c
          (sixVertexFourWidth 0 k) < 2 * Real.pi := by
  let delta := (2 * Real.pi -
    sixVertexSymmetricScatteringBoundaryBound c) / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    have hM :=
      (sixVertexSymmetricScatteringBoundaryBound_lt_two_pi
        (c := c))
    linarith
  have hnhds : Set.Iio delta ∈ nhds (0 : Real) := Iio_mem_nhds hdelta
  have hev :=
    (sixVertexSymmetricTailJacobianTotalError_fourWidth_tendsto_zero
      hc htail).eventually hnhds
  filter_upwards [hev] with k hk
  dsimp [delta] at hk
  linarith

theorem eventually_sixVertexSelectedEvenSymmetricBetheRootJacobian_injective_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    ∀ᶠ k : Nat in atTop, Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian
        (sixVertexFourWidth 0 k) (k + 1) c
        (sixVertexPositiveHalfBetheRoots hc k)) := by
  filter_upwards [eventually_sixVertexSymmetricTailJacobian_margin hc htail]
    with k hmargin
  let p := sixVertexHalfFilledBetheRoots hc k
  let q := sixVertexPositiveHalfBetheRoots hc k
  have hopen : SixVertexOpenRootSimplex p :=
    sixVertexHalfFilledBetheRoots_mem_open hc k
  have hlift : sixVertexEvenSymmetricLift (k + 1) q = p := by
    simpa [q, p, sixVertexPositiveHalfBetheRoots] using
      sixVertexEvenSymmetricLift_projection (k + 1) hopen.2.1
  apply sixVertexEvenSymmetricBetheRootJacobian_injective_tail
    hc htail (by omega) (sixVertexFourWidth_pos 0 k)
    (by unfold sixVertexFourWidth; omega)
  · rw [hlift]
    exact hopen
  · rw [hlift]
    exact sixVertexHalfFilledBetheRoots_is_solution hc k
  · exact hmargin

end
end StatMech.FrontierD
