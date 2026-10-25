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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part5
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem EvenExponentialTypeImaginaryZeros.entireDiskZeroSet_finite
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    Finite (entireDiskZeroSet F R) := by
  let s : Set Complex := entireZeroSet F ∩ closedBall 0 R
  have hs : s.Finite :=
    ((isCompact_closedBall (0 : Complex) R).inter_left
      hF.entireZeroSet_closed_discrete.1).finite
        (hF.entireZeroSet_closed_discrete.2.mono Set.inter_subset_left)
  letI : Finite s := hs.to_subtype
  apply Finite.of_injective
      (fun z : entireDiskZeroSet F R =>
        (⟨z.1, z.2.2, z.2.1⟩ : s))
  intro z w h
  apply Subtype.ext
  exact congrArg (fun x : s => (x : Complex)) h

theorem EvenExponentialTypeImaginaryZeros.entireDiskZeroCopies_finite
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    Finite (entireDiskZeroCopies F R) := by
  letI := hF.entireDiskZeroSet_finite R
  change Finite (Σ z : entireDiskZeroSet F R,
    Fin (analyticOrderNatAt F z.1))
  exact inferInstance

theorem EvenExponentialTypeImaginaryZeros.analyticOrderAt_ne_top
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    analyticOrderAt F z ≠ ⊤ := by
  intro htop
  have hzero : F = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w => hF.analytic w (Set.mem_univ w))).mp htop
  exact hF.value_zero_ne (congrFun hzero 0)

theorem EvenExponentialTypeImaginaryZeros.card_entireDiskZeroCopies_eq_finsum_divisor
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    (Nat.card (entireDiskZeroCopies F R) : Int) =
      ∑ᶠ z : Complex, (MeromorphicOn.divisor F (closedBall 0 R)) z := by
  letI := hF.entireDiskZeroSet_finite R
  letI := hF.entireDiskZeroCopies_finite R
  letI : Fintype (entireDiskZeroSet F R) := Fintype.ofFinite _
  change (Nat.card (Σ z : entireDiskZeroSet F R,
    Fin (analyticOrderNatAt F z.1)) : Int) = _
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  push_cast
  let s : Set Complex := {z | z ∈ closedBall (0 : Complex) R ∧ F z = 0}
  have hs : s.Finite := by
    haveI : Finite s := by
      change Finite (entireDiskZeroSet F R)
      infer_instance
    exact Set.toFinite s
  have hsupport : Function.support
      (fun z : Complex => (MeromorphicOn.divisor F (closedBall 0 R)) z) ⊆
        hs.toFinset := by
    intro z hz
    apply hs.mem_toFinset.mpr
    have hball : z ∈ closedBall (0 : Complex) R := by
      by_contra hnot
      simp [MeromorphicOn.divisor_def, hnot] at hz
    refine ⟨hball, ?_⟩
    by_contra hnonzero
    have horder : analyticOrderAt F z = 0 :=
      (hF.analytic z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr hnonzero
    have hdisc : AnalyticOnNhd Complex F (closedBall 0 R) :=
      hF.analytic.mono (Set.subset_univ _)
    change (MeromorphicOn.divisor F (closedBall 0 R)) z ≠ 0 at hz
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hdisc hball,
      horder] at hz
    simp at hz
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  have hsumSubtype :
      ∑ z ∈ hs.toFinset, (MeromorphicOn.divisor F (closedBall 0 R)) z =
        ∑ z : entireDiskZeroSet F R,
          (MeromorphicOn.divisor F (closedBall 0 R)) z.1 := by
    apply Finset.sum_subtype hs.toFinset
    intro z
    rw [hs.mem_toFinset]
    rfl
  rw [hsumSubtype]
  apply Finset.sum_congr rfl
  intro z _
  have hdisc : AnalyticOnNhd Complex F (closedBall 0 R) :=
    hF.analytic.mono (Set.subset_univ _)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hdisc z.2.1]
  have hfinite := hF.analyticOrderAt_ne_top z.1
  rw [← Nat.cast_analyticOrderNatAt hfinite]
  simp

end
end StatMech.FrontierA
