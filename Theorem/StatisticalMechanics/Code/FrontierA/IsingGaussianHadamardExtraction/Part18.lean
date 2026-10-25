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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part18
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_eq_zeroValue
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    extractedHadamardQuotient hF z = F 0 := by
  let P := hadamardRootProduct (extractedHadamardRoots hF)
  have hQdiff : Differentiable Complex (extractedHadamardQuotient hF) :=
    fun w => hF.extractedHadamardQuotient_analytic w |>.differentiableAt
  have hPdiff : Differentiable Complex P := fun w =>
    (analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable) w (Set.mem_univ w) |>.differentiableAt
  have hPzero : P 0 ≠ 0 := by
    simp [P, hadamardRootProduct, hadamardRootFactor]
  obtain ⟨g, hgdiff, hgexp⟩ := exists_entireLogarithm
    (extractedHadamardQuotient hF) hQdiff
      hF.extractedHadamardQuotient_ne_zero
  have hfactor (w : Complex) : F w = P w * Complex.exp (g w) := by
    rw [hgexp w]
    calc
      F w = extractedHadamardQuotient hF w * P w :=
        (hF.extractedHadamardQuotient_mul_eq w).symm
      _ = P w * extractedHadamardQuotient hF w := mul_comm _ _
  obtain ⟨a, b, hab⟩ := exists_affine_of_matched_entire_exp_growth
    F P g
    (fun w => (hF.analytic w (Set.mem_univ w)).differentiableAt)
    hPdiff hgdiff hPzero hfactor
    hF.prefactor hF.exponentialType
    (hadamardRootProductPrefactor hF) (positiveZeroLogSlopeBound hF)
    hF.prefactor_pos hF.exponentialType_nonneg
    (hadamardRootProductPrefactor_pos hF)
    hF.positiveZeroLogSlopeBound_nonneg hF.norm_le
    hF.norm_hadamardRootProduct_le_exp
  have hQform (w : Complex) :
      extractedHadamardQuotient hF w = Complex.exp (a * w + b) := by
    rw [← hgexp w, hab w]
  have hevenExp :
      (fun w : Complex => Complex.exp (a * (-w) + b)) =
        fun w => Complex.exp (a * w + b) := by
    funext w
    rw [← hQform (-w), ← hQform w]
    exact hF.extractedHadamardQuotient_even w
  have hleft : HasDerivAt
      (fun w : Complex => Complex.exp (a * (-w) + b))
      (Complex.exp b * (-a)) 0 := by
    have hinner : HasDerivAt (fun w : Complex => a * (-w) + b) (-a) 0 := by
      convert (((hasDerivAt_id (0 : Complex)).neg.const_mul a).add_const b) using 1 <;>
        ring
    convert (Complex.hasDerivAt_exp (a * (-(0 : Complex)) + b)).comp 0 hinner using 1 <;>
      simp
  have hright : HasDerivAt
      (fun w : Complex => Complex.exp (a * w + b))
      (Complex.exp b * a) 0 := by
    have hinner : HasDerivAt (fun w : Complex => a * w + b) a 0 := by
      convert (((hasDerivAt_id (0 : Complex)).const_mul a).add_const b) using 1 <;>
        ring
    convert (Complex.hasDerivAt_exp (a * (0 : Complex) + b)).comp 0 hinner using 1 <;>
      simp
  have hderiv := congrArg (fun f : (Complex → Complex) => deriv f 0) hevenExp
  change deriv (fun w : Complex => Complex.exp (a * (-w) + b)) 0 =
    deriv (fun w : Complex => Complex.exp (a * w + b)) 0 at hderiv
  rw [hleft.deriv, hright.deriv] at hderiv
  have ha : a = 0 := by
    by_contra hane
    have hneg : -(a * Complex.exp b) = a * Complex.exp b := by
      simpa [mul_comm] using hderiv
    have htwo : (2 : Complex) * (a * Complex.exp b) = 0 := by
      calc
        (2 : Complex) * (a * Complex.exp b) =
            a * Complex.exp b + a * Complex.exp b := by ring
        _ = -(a * Complex.exp b) + a * Complex.exp b := by rw [hneg]
        _ = 0 := neg_add_cancel _
    exact (mul_ne_zero (by norm_num)
      (mul_ne_zero hane (Complex.exp_ne_zero b))) htwo
  calc
    extractedHadamardQuotient hF z = Complex.exp (a * z + b) := hQform z
    _ = Complex.exp b := by rw [ha]; simp
    _ = extractedHadamardQuotient hF 0 := by
      rw [hQform 0, ha]
      simp
    _ = F 0 := hF.extractedHadamardQuotient_zero


end
end StatMech.FrontierA
