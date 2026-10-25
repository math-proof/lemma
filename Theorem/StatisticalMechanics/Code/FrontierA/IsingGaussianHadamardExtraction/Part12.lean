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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part12
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem EvenExponentialTypeImaginaryZeros.positiveZeroLogSlopeBound_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 ≤ positiveZeroLogSlopeBound hF := by
  unfold positiveZeroLogSlopeBound
  exact add_nonneg
    (add_nonneg hF.smallZeroLogSlopeBound_nonneg
      (mul_nonneg (by norm_num) (hadamardZeroCountIntercept_nonneg hF)))
    (mul_nonneg (by norm_num) (hadamardZeroCountSlope_nonneg hF))

theorem EvenExponentialTypeImaginaryZeros.positiveZero_logSlope_le
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 1 ≤ R) :
    (∑' q : positiveImaginaryZeroCopies F,
      2 * R / (q.1.1 ^ 2 + R ^ 2)) ≤
      positiveZeroLogSlopeBound hF := by
  let slope : positiveImaginaryZeroCopies F → Real := fun q =>
    2 * R / (q.1.1 ^ 2 + R ^ 2)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hslope : Summable slope := by
    apply Summable.of_nonneg_of_le
      (fun q => div_nonneg (mul_nonneg (by norm_num) hRpos.le)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (fun q => ?_)
      (hF.positiveImaginaryZeroMass_summable.mul_left (2 * R))
    dsimp [slope]
    unfold positiveImaginaryZeroMass
    have hy : q.1.1 ≠ 0 := q.1.2.1.ne'
    calc
      2 * R / (q.1.1 ^ 2 + R ^ 2) ≤ 2 * R / q.1.1 ^ 2 := by
        exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hRpos.le)
          (sq_pos_of_pos q.1.2.1) (le_add_of_nonneg_right (sq_nonneg R))
      _ = 2 * R * (q.1.1 ^ 2)⁻¹ := by rw [div_eq_mul_inv]
  let large : Set (positiveImaginaryZeroCopies F) := {q | 1 ≤ q.1.1}
  let small : Set (positiveImaginaryZeroCopies F) := {q | q.1.1 < 1}
  have hcompl : largeᶜ = small := by
    ext q
    change (¬1 ≤ q.1.1) ↔ q.1.1 < 1
    exact not_le
  have hsplit := hslope.tsum_subtype_add_tsum_subtype_compl large
  rw [hcompl] at hsplit
  letI : Finite small := by
    exact hF.smallZeroCopies_finite
  have hinvSmall : Summable (fun q : small => (q.1.1.1)⁻¹) := by
    exact summable_of_finite_support (Set.finite_univ.subset (Set.subset_univ _))
  have hsmall : (∑' q : small, slope q.1) ≤
      smallZeroLogSlopeBound (F := F) := by
    change (∑' q : small, slope q.1) ≤ ∑' q : small, (q.1.1.1)⁻¹
    apply (hslope.subtype small).tsum_le_tsum
    · intro q
      dsimp [slope]
      have hy : 0 < q.1.1.1 := q.1.1.2.1
      have hden : 0 < q.1.1.1 ^ 2 + R ^ 2 := by positivity
      rw [inv_eq_one_div, le_div_iff₀ hy, div_mul_eq_mul_div,
        div_le_iff₀ hden]
      nlinarith [sq_nonneg (R - q.1.1.1)]
    · exact hinvSmall
  have hlarge : (∑' q : large, slope q.1) ≤
      13 * hadamardZeroCountIntercept hF +
        18 * hadamardZeroCountSlope hF := by
    exact hF.largeZero_logSlope_le hR
  change (∑' q, slope q) ≤ _
  rw [← hsplit]
  unfold positiveZeroLogSlopeBound
  linarith

theorem EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_le_linear
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 1 ≤ R) :
    positiveZeroRadialLog (F := F) R ≤
      positiveZeroRadialLog (F := F) 1 +
        positiveZeroLogSlopeBound hF * (R - 1) := by
  have hdiff : Differentiable Real (positiveZeroRadialLog (F := F)) :=
    fun x => (hF.positiveZeroRadialLog_hasDerivAt x).differentiableAt
  rw [add_comm]
  rw [← sub_le_iff_le_add]
  apply (convex_Ici (1 : Real)).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuous.continuousOn hdiff.differentiableOn
  · intro x hx
    have hxone : 1 ≤ x := interior_subset hx
    rw [(hF.positiveZeroRadialLog_hasDerivAt x).deriv]
    exact hF.positiveZero_logSlope_le hxone
  · exact Set.mem_Ici.mpr le_rfl
  · exact Set.mem_Ici.mpr hR
  · exact hR

theorem EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_copies_tprod
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    hadamardRootProduct (extractedHadamardRoots hF) z =
      ∏' q : positiveImaginaryZeroCopies F,
        (1 + (positiveImaginaryZeroMass q : Complex) * z ^ 2) := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  let encode : positiveImaginaryZeroCopies F → Nat :=
    @Encodable.encode (positiveImaginaryZeroCopies F)
      (positiveImaginaryZeroCopiesEncodable hF)
  let f : Nat → Complex := fun n =>
    hadamardRootFactor (extractedHadamardRoots hF) n z
  have hsupport : Function.mulSupport f ⊆ Set.range encode := by
    intro n hn
    by_contra hnrange
    have hroot : extractedHadamardRoots hF n = 0 := by
      apply encodedCountableSequence_eq_zero_of_notMem_range
        (α := positiveImaginaryZeroCopies F) positiveImaginaryZeroMass n
      simpa [encode, positiveImaginaryZeroCopiesEncodable,
        extractedHadamardRoots] using hnrange
    exact hn (by simp [f, hadamardRootFactor, hroot])
  have hreindex := (@Encodable.encode_injective
    (positiveImaginaryZeroCopies F) (positiveImaginaryZeroCopiesEncodable hF)).tprod_eq
      (f := f) hsupport
  rw [hadamardRootProduct]
  rw [← hreindex]
  apply tprod_congr
  intro q
  simp [f, hadamardRootFactor, encode, extractedHadamardRoots_encode]

theorem EvenExponentialTypeImaginaryZeros.norm_hadamardRootProduct_le_radialLog
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    ‖hadamardRootProduct (extractedHadamardRoots hF) z‖ ≤
      Real.exp (positiveZeroRadialLog (F := F) ‖z‖) := by
  let g : positiveImaginaryZeroCopies F → Complex := fun q =>
    1 + (positiveImaginaryZeroMass q : Complex) * z ^ 2
  let a : positiveImaginaryZeroCopies F → Real := fun q =>
    1 + ‖z‖ ^ 2 * positiveImaginaryZeroMass q
  have hmassScaled : Summable (fun q : positiveImaginaryZeroCopies F =>
      ‖z‖ ^ 2 * positiveImaginaryZeroMass q) :=
    hF.positiveImaginaryZeroMass_summable.mul_left (‖z‖ ^ 2)
  have hpert : Summable (fun q : positiveImaginaryZeroCopies F =>
      ‖(positiveImaginaryZeroMass q : Complex) * z ^ 2‖) := by
    apply hmassScaled.congr
    intro q
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (positiveImaginaryZeroMass_pos q), norm_pow]
    ring
  have hgMult : Multipliable g := by
    apply multipliable_one_add_of_summable
    exact hpert
  have hterm : ∀ q, ‖g q‖ ≤ a q := by
    intro q
    dsimp [g, a]
    calc
      ‖1 + (positiveImaginaryZeroMass q : Complex) * z ^ 2‖ ≤
          1 + ‖(positiveImaginaryZeroMass q : Complex) * z ^ 2‖ := by
        simpa only [norm_one] using norm_add_le (1 : Complex)
          ((positiveImaginaryZeroMass q : Complex) * z ^ 2)
      _ = 1 + ‖z‖ ^ 2 * positiveImaginaryZeroMass q := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (positiveImaginaryZeroMass_pos q), norm_pow]
        ring
  by_cases hzero : ∃ q, g q = 0
  · obtain ⟨q, hq⟩ := hzero
    rw [hF.hadamardRootProduct_eq_copies_tprod z,
      tprod_of_exists_eq_zero ⟨q, hq⟩, norm_zero]
    positivity
  · have hall : ∀ q, g q ≠ 0 := by simpa only [not_exists] using hzero
    have hlogG : Summable (fun q => Real.log ‖g q‖) := by
      simpa [g] using hpert.summable_log_norm_one_add
    have hlogA : Summable (fun q => Real.log (a q)) := by
      simpa [a] using Real.summable_log_one_add_of_summable hmassScaled
    have hlogTerm : ∀ q, Real.log ‖g q‖ ≤ Real.log (a q) := by
      intro q
      have haPos : 0 < a q := by
        dsimp [a]
        nlinarith [sq_nonneg ‖z‖, positiveImaginaryZeroMass_pos q]
      apply Real.strictMonoOn_log.monotoneOn
        (norm_pos_iff.mpr (hall q)) haPos (hterm q)
    rw [hF.hadamardRootProduct_eq_copies_tprod z, hgMult.norm_tprod,
      ← Real.rexp_tsum_eq_tprod (fun q => norm_pos_iff.mpr (hall q)) hlogG]
    exact Real.exp_le_exp.mpr (hlogG.tsum_le_tsum hlogTerm hlogA)

end
end StatMech.FrontierA
