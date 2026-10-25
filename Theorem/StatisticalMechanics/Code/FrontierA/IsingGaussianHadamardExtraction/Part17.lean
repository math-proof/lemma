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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part17
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem EvenExponentialTypeImaginaryZeros.hadamardRootProduct_order_ne_top
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) z ≠ ⊤ := by
  rw [analyticOrderAt_hadamardRootProduct_eq_card
    (extractedHadamardRoots_nonneg hF)
    hF.extractedHadamardRoots_summable]
  simp

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_analytic
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    AnalyticAt Complex (extractedHadamardQuotient hF) z := by
  apply analyticAt_entireOrderMatchedQuotient
    (fun w => hF.analytic w (Set.mem_univ w))
    (fun w => (analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable) w (Set.mem_univ w))
    (fun w => (hF.analyticOrderAt_hadamardRootProduct_eq w).symm)
    hF.hadamardRootProduct_order_ne_top z

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_ne_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    extractedHadamardQuotient hF z ≠ 0 := by
  apply entireOrderMatchedQuotient_ne_zero
    (fun w => hF.analytic w (Set.mem_univ w))
    (fun w => (analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable) w (Set.mem_univ w))
    (fun w => (hF.analyticOrderAt_hadamardRootProduct_eq w).symm)
    hF.hadamardRootProduct_order_ne_top z

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_mul_eq
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    extractedHadamardQuotient hF z *
        hadamardRootProduct (extractedHadamardRoots hF) z = F z := by
  exact entireOrderMatchedQuotient_mul_eq
    (fun w => hF.analytic w (Set.mem_univ w))
    (fun w => (analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable) w (Set.mem_univ w))
    (fun w => (hF.analyticOrderAt_hadamardRootProduct_eq w).symm) z

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_even
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    extractedHadamardQuotient hF (-z) = extractedHadamardQuotient hF z := by
  let P := hadamardRootProduct (extractedHadamardRoots hF)
  let Q := extractedHadamardQuotient hF
  have hQanalytic : AnalyticOnNhd Complex Q Set.univ := fun w _ =>
    hF.extractedHadamardQuotient_analytic w
  have hQnegAnalytic : AnalyticOnNhd Complex (fun w => Q (-w)) Set.univ := by
    intro w _
    exact (hQanalytic (-w) (Set.mem_univ _)).comp (by fun_prop)
  have hlocal : (fun w => Q (-w)) =ᶠ[nhds (0 : Complex)] Q := by
    have hnhd : hadamardRootNeighborhood (extractedHadamardRoots hF) ∈
        nhds (0 : Complex) :=
      (isOpen_hadamardRootNeighborhood _).mem_nhds
        (zero_mem_hadamardRootNeighborhood
          (extractedHadamardRoots_nonneg hF))
    filter_upwards [hnhd] with w hw
    apply mul_right_cancel₀ (hadamardRootProduct_ne_zero
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable hw)
    calc
      Q (-w) * P w = Q (-w) * P (-w) := by
        rw [show P (-w) = P w by
          exact hadamardRootProduct_neg (extractedHadamardRoots hF) w]
      _ = F (-w) := hF.extractedHadamardQuotient_mul_eq (-w)
      _ = F w := hF.even w
      _ = Q w * P w := (hF.extractedHadamardQuotient_mul_eq w).symm
  have hglobal : (fun w => Q (-w)) = Q :=
    hQnegAnalytic.eq_of_eventuallyEq hQanalytic hlocal
  exact congrFun hglobal z

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    extractedHadamardQuotient hF 0 = F 0 := by
  have hmul := hF.extractedHadamardQuotient_mul_eq 0
  simpa [hadamardRootProduct, hadamardRootFactor] using hmul


theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_eq_zeroValue_of_growth
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {A B : Real} (hA : 0 < A) (hB : 0 ≤ B)
    (hgrowth : ∀ z,
      ‖extractedHadamardQuotient hF z‖ ≤ A * Real.exp (B * ‖z‖))
    (z : Complex) :
    extractedHadamardQuotient hF z = F 0 := by
  have hQdiff : Differentiable Complex (extractedHadamardQuotient hF) :=
    fun w => hF.extractedHadamardQuotient_analytic w |>.differentiableAt
  obtain ⟨g, hgdiff, hgexp⟩ := exists_entireLogarithm
    (extractedHadamardQuotient hF) hQdiff
      hF.extractedHadamardQuotient_ne_zero
  obtain ⟨a, b, hab⟩ := exists_affine_of_entire_exp_growth
    g hgdiff A B hA hB (fun w => by simpa [hgexp w] using hgrowth w)
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
