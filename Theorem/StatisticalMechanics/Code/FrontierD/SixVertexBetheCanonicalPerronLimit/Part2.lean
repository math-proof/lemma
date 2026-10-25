/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral_le
    {c : Real} (hc : 2 < c) {lower : Real} (hlower : 0 < lower)
    {k : Nat}
    (hdensity : ∀ x : Real,
      lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc k) x)
    (hepsilon : 0 < sixVertexCanonicalPerronLogEpsilon hc k) :
    |sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c
            (sixVertexCanonicalPerronLogEpsilon hc k)) k -
        sixVertexCanonicalPerronRegularizedIntegral hc k| ≤
      (sixVertexRegularizedBetheLogLipschitzConstant c
          (sixVertexCanonicalPerronLogEpsilon hc k) : Real) *
        sixVertexFiniteRootDensityUniformBound c *
        (1 / ((sixVertexFourWidth 0 k : Real) * lower)) *
        (2 * Real.pi) +
      sixVertexCanonicalPerronRegularizedBound hc k *
        (sixVertexCanonicalDensityPerronGauge hc k /
          ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c)) * (2 * Real.pi) := by
  let epsilon := sixVertexCanonicalPerronLogEpsilon hc k
  let f := sixVertexRegularizedBetheLogKernel c epsilon
  let C := sixVertexRegularizedBetheLogLipschitzConstant c epsilon
  let B := sixVertexCanonicalPerronRegularizedBound hc k
  let p := sixVertexCanonicalDensityPerronBetheRoots hc k
  let rhoN := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
    ((k + 1) + (k + 1)) p
  let I := ∫ y in -Real.pi..Real.pi, f y * rhoN y
  let target := sixVertexCanonicalPerronRegularizedIntegral hc k
  have hC : LipschitzWith C f := by
    exact lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon
  have hf : Continuous f := hC.continuous
  have hbound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ B := by
    intro x hx
    have hdist : |f x - f 0| ≤ (C : Real) * |x| := by
      simpa only [Real.norm_eq_abs, sub_zero] using hC.norm_sub_le x 0
    have hxabs : |x| ≤ Real.pi := abs_le.mpr hx
    calc
      |f x| = |(f x - f 0) + f 0| := by ring_nf
      _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
      _ ≤ (C : Real) * |x| + |f 0| := by linarith
      _ ≤ (C : Real) * Real.pi + |f 0| := by gcongr
      _ = B := by
        dsimp [B, sixVertexCanonicalPerronRegularizedBound, f, C, epsilon]
        ring
  have hB : 0 ≤ B := by
    dsimp [B, sixVertexCanonicalPerronRegularizedBound]
    positivity
  have hN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
  have hn : 0 < (k + 1) + (k + 1) := by omega
  have hhalf : sixVertexFourWidth 0 k =
      2 * ((k + 1) + (k + 1)) := by
    unfold sixVertexFourWidth
    omega
  have hquad :=
    abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_lower
      hc hN hn hhalf (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
      (sixVertexCanonicalDensityPerronBetheRoots_is_solution hc k)
      hlower hdensity hf hC
      (periodic_sixVertexRegularizedBetheLogKernel c epsilon)
  have hint := abs_sixVertexCanonicalDensityIntegral_sub_fourier_le
    hc hf hB hbound k
  change |sixVertexCanonicalDensityPerronEmpiricalObservable hc f k - I| ≤
    (C : Real) * sixVertexFiniteRootDensityUniformBound c *
      (1 / ((sixVertexFourWidth 0 k : Real) * lower)) *
        (2 * Real.pi) at hquad
  change |I - target| ≤ B *
    (sixVertexCanonicalDensityPerronGauge hc k /
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c)) * (2 * Real.pi) at hint
  change |sixVertexCanonicalDensityPerronEmpiricalObservable hc f k - target| ≤ _
  exact (abs_sub_le
    (sixVertexCanonicalDensityPerronEmpiricalObservable hc f k)
    I target).trans (add_le_add hquad hint)

end
end StatMech.FrontierD
