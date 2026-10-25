/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.HadamardQuadraticFactorOrder
import Theorem.StatisticalMechanics.Code.FrontierA.EntireOrderMatchedQuotient
import Theorem.StatisticalMechanics.Code.FrontierA.EntireZeroFreeLogarithm
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialLogAffine
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialCharacteristicAffine
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Lindelof
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part13
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem hadamardRootProductPrefactor_pos
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 < hadamardRootProductPrefactor hF := Real.exp_pos _

theorem EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_le_affine
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) (hR : 0 ≤ R) :
    positiveZeroRadialLog (F := F) R ≤
      positiveZeroRadialLog (F := F) 1 +
        positiveZeroLogSlopeBound hF * R := by
  by_cases hRone : 1 ≤ R
  · have hlin := hF.positiveZeroRadialLog_le_linear hRone
    nlinarith [hF.positiveZeroLogSlopeBound_nonneg]
  · have hRle : R ≤ 1 := le_of_not_ge hRone
    have hR2 : R ^ 2 ≤ (1 : Real) ^ 2 :=
      (sq_le_sq₀ hR (by norm_num)).2 hRle
    have hterm : ∀ q : positiveImaginaryZeroCopies F,
        Real.log (1 + R ^ 2 * positiveImaginaryZeroMass q) ≤
          Real.log (1 + 1 ^ 2 * positiveImaginaryZeroMass q) := by
      intro q
      have hm : 0 ≤ positiveImaginaryZeroMass q :=
        (positiveImaginaryZeroMass_pos q).le
      have hleftPos : 0 < 1 + R ^ 2 * positiveImaginaryZeroMass q := by
        nlinarith [mul_nonneg (sq_nonneg R) hm]
      have hrightPos : 0 < 1 + 1 ^ 2 * positiveImaginaryZeroMass q := by
        nlinarith
      apply Real.strictMonoOn_log.monotoneOn
        hleftPos hrightPos
      gcongr
    have hsum := (hF.positiveZeroRadialLog_summable R).tsum_le_tsum hterm
      (hF.positiveZeroRadialLog_summable 1)
    calc
      positiveZeroRadialLog (F := F) R ≤
          positiveZeroRadialLog (F := F) 1 := hsum
      _ ≤ positiveZeroRadialLog (F := F) 1 +
          positiveZeroLogSlopeBound hF * R := by
        exact le_add_of_nonneg_right
          (mul_nonneg hF.positiveZeroLogSlopeBound_nonneg hR)

theorem EvenExponentialTypeImaginaryZeros.norm_hadamardRootProduct_le_exp
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    ‖hadamardRootProduct (extractedHadamardRoots hF) z‖ ≤
      hadamardRootProductPrefactor hF *
        Real.exp (positiveZeroLogSlopeBound hF * ‖z‖) := by
  calc
    ‖hadamardRootProduct (extractedHadamardRoots hF) z‖ ≤
        Real.exp (positiveZeroRadialLog (F := F) ‖z‖) :=
      hF.norm_hadamardRootProduct_le_radialLog z
    _ ≤ Real.exp (positiveZeroRadialLog (F := F) 1 +
        positiveZeroLogSlopeBound hF * ‖z‖) :=
      Real.exp_le_exp.mpr (hF.positiveZeroRadialLog_le_affine ‖z‖ (norm_nonneg z))
    _ = hadamardRootProductPrefactor hF *
        Real.exp (positiveZeroLogSlopeBound hF * ‖z‖) := by
      rw [Real.exp_add]
      rfl

theorem hasProdLocallyUniformlyOn_hadamardRootFactor
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) :
    HasProdLocallyUniformlyOn (hadamardRootFactor roots)
      (hadamardRootProduct roots) Set.univ := by
  rcases multipliableLocallyUniformlyOn_hadamardRootFactor hroots hsum with
    ⟨g, hg⟩
  have heq : g = hadamardRootProduct roots := by
    funext z
    have hp : HasProd (fun n => hadamardRootFactor roots n z) (g z) :=
      hg.tendsto_at (Set.mem_univ z)
    exact hp.tprod_eq.symm
  rw [← heq]
  exact hg

theorem analyticOnNhd_hadamardRootProduct
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) :
    AnalyticOnNhd Complex (hadamardRootProduct roots) Set.univ := by
  have hprod := hasProdLocallyUniformlyOn_hadamardRootFactor hroots hsum
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hprod
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  apply hprod.differentiableOn _ isOpen_univ
  exact Filter.Eventually.of_forall fun s => by
    intro z _hz
    apply DifferentiableAt.differentiableWithinAt
    unfold hadamardRootFactor
    fun_prop

theorem hadamardVanishingIndices_finite
    {roots : Nat → Real} (hsum : Summable roots) (z : Complex) :
    {n | hadamardRootFactor roots n z = 0}.Finite := by
  have hroots0 : Tendsto (fun n => (roots n : Complex)) cofinite (nhds 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp
      hsum.tendsto_cofinite_zero
  have hfactors1 : Tendsto (fun n => hadamardRootFactor roots n z)
      cofinite (nhds 1) := by
    convert tendsto_const_nhds.add (hroots0.mul_const (z ^ 2)) using 1 <;> simp
  have hevent : ∀ᶠ n in cofinite, hadamardRootFactor roots n z ≠ 0 := by
    filter_upwards [hfactors1.eventually
      (ball_mem_nhds (1 : Complex) zero_lt_one)] with n hn
    intro hzero
    rw [hzero] at hn
    norm_num [mem_ball] at hn
  simpa only [not_ne_iff] using Filter.eventually_cofinite.mp hevent


end
end StatMech.FrontierA
