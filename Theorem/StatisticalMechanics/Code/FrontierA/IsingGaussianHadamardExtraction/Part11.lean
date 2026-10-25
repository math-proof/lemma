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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part11
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem EvenExponentialTypeImaginaryZeros.smallZeroLogSlopeBound_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 ≤ smallZeroLogSlopeBound (F := F) := by
  apply tsum_nonneg
  intro q
  exact inv_nonneg.mpr q.1.1.2.1.le

theorem EvenExponentialTypeImaginaryZeros.smallZeroCopies_finite
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    Finite {q : positiveImaginaryZeroCopies F // q.1.1 < 1} := by
  let target := positiveImaginaryZeroCopiesBelow F 1
  letI : Finite target :=
    hF.positiveImaginaryZeroCopiesBelow_finite 1 |>.to_subtype
  let embed : {q : positiveImaginaryZeroCopies F // q.1.1 < 1} → target :=
    fun q => ⟨q.1, q.2.le⟩
  exact Finite.of_injective embed (by
    intro q r h
    apply Subtype.ext
    exact congrArg (fun x : target => x.1) h)

theorem EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_summable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    Summable (fun q : positiveImaginaryZeroCopies F =>
      Real.log (1 + R ^ 2 * positiveImaginaryZeroMass q)) := by
  apply Real.summable_log_one_add_of_summable
  exact hF.positiveImaginaryZeroMass_summable.mul_left (R ^ 2)

theorem positiveZeroRadialLog_term_hasDerivAt
    {F : Complex → Complex} (q : positiveImaginaryZeroCopies F) (R : Real) :
    HasDerivAt
      (fun x => Real.log (1 + x ^ 2 * positiveImaginaryZeroMass q))
      (2 * R / (q.1.1 ^ 2 + R ^ 2)) R := by
  have hinner : HasDerivAt
      (fun x : Real => 1 + x ^ 2 * positiveImaginaryZeroMass q)
      (2 * R * positiveImaginaryZeroMass q) R := by
    convert (((hasDerivAt_id R).pow 2).mul_const
      (positiveImaginaryZeroMass q) |>.const_add 1) using 1 <;>
        simp [id] <;> ring
  have hpos : 0 < 1 + R ^ 2 * positiveImaginaryZeroMass q := by
    nlinarith [sq_nonneg R, positiveImaginaryZeroMass_pos q]
  convert hinner.log hpos.ne' using 1
  unfold positiveImaginaryZeroMass
  have hy : q.1.1 ≠ 0 := q.1.2.1.ne'
  field_simp

theorem EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_hasDerivAt
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    HasDerivAt (positiveZeroRadialLog (F := F))
      (∑' q : positiveImaginaryZeroCopies F,
        2 * R / (q.1.1 ^ 2 + R ^ 2)) R := by
  let M : Real := |R| + 1
  let u : positiveImaginaryZeroCopies F → Real := fun q =>
    2 * M * positiveImaginaryZeroMass q
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hu : Summable u :=
    hF.positiveImaginaryZeroMass_summable.mul_left (2 * M)
  change HasDerivAt (fun x => ∑' q : positiveImaginaryZeroCopies F,
    Real.log (1 + x ^ 2 * positiveImaginaryZeroMass q))
    (∑' q : positiveImaginaryZeroCopies F,
      2 * R / (q.1.1 ^ 2 + R ^ 2)) R
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun q x => Real.log (1 + x ^ 2 * positiveImaginaryZeroMass q))
    (g' := fun q x => 2 * x / (q.1.1 ^ 2 + x ^ 2))
    (t := Set.Ioo (-M) M) (y₀ := 0) (y := R) hu
    (isOpen_Ioo : IsOpen (Set.Ioo (-M) M)) isPreconnected_Ioo
  · intro q x _hx
    exact positiveZeroRadialLog_term_hasDerivAt q x
  · intro q x hx
    rw [Real.norm_eq_abs]
    have hxabs : |x| ≤ M := by
      rw [abs_le]
      exact ⟨hx.1.le, hx.2.le⟩
    dsimp [u]
    have hy2 : 0 < q.1.1 ^ 2 := sq_pos_of_pos q.1.2.1
    have hden : 0 < q.1.1 ^ 2 + x ^ 2 := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
      abs_of_pos hden]
    norm_num
    calc
      2 * |x| / (q.1.1 ^ 2 + x ^ 2) ≤
          2 * |x| / q.1.1 ^ 2 := by
        exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (abs_nonneg x))
          hy2 (le_add_of_nonneg_right (sq_nonneg x))
      _ =
          2 * |x| * positiveImaginaryZeroMass q := by
        unfold positiveImaginaryZeroMass
        rw [div_eq_mul_inv]
      _ ≤ 2 * M * positiveImaginaryZeroMass q := by
        have hm : 0 ≤ positiveImaginaryZeroMass q :=
          (positiveImaginaryZeroMass_pos q).le
        gcongr
  · exact ⟨neg_lt_zero.mpr hMpos, hMpos⟩
  · simpa using (summable_zero : Summable
      (fun _ : positiveImaginaryZeroCopies F => (0 : Real)))
  · exact ⟨by dsimp [M]; linarith [neg_abs_le R], by
      dsimp [M]
      linarith [le_abs_self R]⟩

end
end StatMech.FrontierA
