/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityComponent
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedDensityCauchy
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
import Mathlib.Algebra.Field.Periodic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate


namespace StatMech.FrontierD

noncomputable section

theorem abs_finiteRootDensity_sub_continuumDensity_weighted_le_of_lower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {rho : Real → Real} (hrho : Continuous rho)
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {lower E : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x)
    (hE : 0 ≤ E)
    (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N (n + 1) p y - rho y)| ≤ E)
    (x : Real) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N (n + 1) p x - rho x)| ≤
      sixVertexRootDensityContractionRate c * E +
        sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
  let rhoN := sixVertexFiniteRootDensity c N (n + 1) p
  let e : Real → Real := fun y =>
    sixVertexRootDensityWeight c y * (rhoN y - rho y)
  let D := sixVertexFiniteConvolutionDefect c N (n + 1) p
  let IN : Real → Real := fun z =>
    ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c z y * rhoN y
  let IR : Real → Real := fun z =>
    ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c z y * rho y
  let Q := sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c *
      (1 / ((N : Real) * lower)) * (2 * Real.pi)
  have hweightCont : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have hrhoN : Continuous rhoN :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have he : Continuous e := hweightCont.mul (hrhoN.sub hrho)
  have hrhoNInt : IntervalIntegrable rhoN MeasureTheory.volume
      (-Real.pi) Real.pi := hrhoN.intervalIntegrable _ _
  have hrhoInt : IntervalIntegrable rho MeasureTheory.volume
      (-Real.pi) Real.pi := hrho.intervalIntegrable _ _
  have heMass : ∫ y in -Real.pi..Real.pi,
      e y / sixVertexRootDensityWeight c y = 0 := by
    have heq : (fun y => e y / sixVertexRootDensityWeight c y) =
        fun y => rhoN y - rho y := by
      funext y
      dsimp [e]
      field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
    rw [heq, intervalIntegral.integral_sub hrhoNInt hrhoInt,
      intervalIntegral_halfFilledFiniteRootDensity hc hN hhalf p, hrhoMass]
    ring
  have hcontract := sixVertexRootDensityKernel_contraction hc he hE heMass
    (by simpa [e, rhoN] using hbound) x
  have hmesh := sixVertexCyclicRootPartition_mesh_of_finiteDensityLower
    hc hN hhalf hopen hsol hlower hdensity
  have hD : |D x| ≤ Q := by
    exact abs_empiricalKernel_sub_finiteDensityIntegral_le_of_mesh
      hc hN hcount hhalf hopen hsol hmesh x
  have hkernel : Continuous (sixVertexRootDensityKernel c x) :=
    (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
  have hNInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y * rhoN y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hkernel.mul hrhoN).intervalIntegrable _ _
  have hRInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hkernel.mul hrho).intervalIntegrable _ _
  have hJ : (∫ y in -Real.pi..Real.pi,
      (sixVertexRootDensityKernel c x y /
        sixVertexRootDensityWeight c y) * e y) = IN x - IR x := by
    rw [show (fun y =>
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
      fun y => sixVertexRootDensityKernel c x y * (rhoN y - rho y) by
        funext y
        dsimp [e]
        field_simp [(sixVertexRootDensityWeight_pos hc y).ne']]
    rw [show (fun y => sixVertexRootDensityKernel c x y * (rhoN y - rho y)) =
      fun y => sixVertexRootDensityKernel c x y * rhoN y -
        sixVertexRootDensityKernel c x y * rho y by funext y; ring]
    exact intervalIntegral.integral_sub hNInt hRInt
  have hNEq : sixVertexRootDensityWeight c x * rhoN x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) * IN x - (1 / (2 * Real.pi)) * D x := by
    have hfinite := sixVertexRootDensityWeight_mul_finiteRootDensity hc hN p x
    dsimp [rhoN, IN, D, sixVertexFiniteConvolutionDefect]
    rw [hfinite]
    field_simp [Real.pi_ne_zero,
      (by exact_mod_cast hN.ne' : (N : Real) ≠ 0)]
    ring
  have hREq : sixVertexRootDensityWeight c x * rho x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) * IR x := hrhoEq x hx
  have heqPoint : e x =
      -(1 / (2 * Real.pi)) * (IN x - IR x) -
        (1 / (2 * Real.pi)) * D x := by
    dsimp [e]
    rw [mul_sub, hNEq, hREq]
    ring
  change |e x| ≤ _
  rw [heqPoint, ← hJ]
  calc
    |-(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y) -
        (1 / (2 * Real.pi)) * D x| ≤
      |(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y)| +
        |(1 / (2 * Real.pi)) * D x| := by
      simpa [abs_neg] using abs_add_le
        (-(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y))
        (-(1 / (2 * Real.pi)) * D x)
    _ ≤ sixVertexRootDensityContractionRate c * E + Q / (2 * Real.pi) := by
      apply add_le_add hcontract
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
      calc
        (1 / (2 * Real.pi)) * |D x| ≤
            (1 / (2 * Real.pi)) * Q :=
          mul_le_mul_of_nonneg_left hD (by positivity)
        _ = Q / (2 * Real.pi) := by ring
    _ = sixVertexRootDensityContractionRate c * E +
        sixVertexFiniteDensityContinuumErrorOfLower c N lower := by rfl

end
end StatMech.FrontierD
