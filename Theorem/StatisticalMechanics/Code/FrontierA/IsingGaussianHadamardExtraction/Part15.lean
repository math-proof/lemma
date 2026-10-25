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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part15
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem analyticOnNhd_hadamardRootProductAway
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (S : Finset Nat) :
    AnalyticOnNhd Complex (hadamardRootProductAway (roots := roots) S) Set.univ := by
  let roots' : Nat → Real := fun n => if n ∈ S then 0 else roots n
  have hroots' : ∀ n, 0 ≤ roots' n := by
    intro n
    dsimp [roots']
    split <;> simp_all
  have hsum' : Summable roots' := by
    have hi := hsum.indicator (S : Set Nat)ᶜ
    apply hi.congr
    intro n
    by_cases hn : n ∈ S <;> simp [roots', Set.indicator, hn]
  have ha := analyticOnNhd_hadamardRootProduct hroots' hsum'
  convert ha using 1
  funext w
  unfold hadamardRootProductAway hadamardRootProduct
  apply tprod_congr
  intro n
  by_cases hn : n ∈ S <;>
    simp [roots', hadamardRootFactor, hn]

theorem hadamardRootProduct_eq_finset_prod_mul_away
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (S : Finset Nat) (w : Complex) :
    hadamardRootProduct roots w =
      (∏ n ∈ S, hadamardRootFactor roots n w) *
        hadamardRootProductAway (roots := roots) S w := by
  let f : Nat → Complex := fun n => hadamardRootFactor roots n w
  let fS : Nat → Complex := fun n => if n ∈ S then f n else 1
  let fSc : Nat → Complex := fun n => if n ∈ S then 1 else f n
  have hmultS : Multipliable fS := by
    apply multipliable_of_finite_mulSupport
    apply S.finite_toSet.subset
    intro n hn
    by_contra hnS
    change n ∉ S at hnS
    change fS n ≠ 1 at hn
    exact hn (if_neg hnS)
  have hmultSc : Multipliable fSc := by
    let delta : Nat → Complex := fun n =>
      if n ∈ S then 0 else (roots n : Complex) * w ^ 2
    have hi := (summable_norm_hadamardRootFactor_sub_one hroots hsum w).indicator
      (S : Set Nat)ᶜ
    have hdelta : Summable (fun n => ‖delta n‖) := by
      apply hi.congr
      intro n
      by_cases hn : n ∈ S <;>
        simp [delta, hn, Set.indicator]
    have hm := multipliable_one_add_of_summable hdelta
    apply hm.congr
    intro n
    by_cases hn : n ∈ S <;>
      simp [fSc, f, delta, hadamardRootFactor, hn]
  change (∏' n, f n) = (∏ n ∈ S, f n) * ∏' n, fSc n
  calc
    (∏' n, f n) = ∏' n, fS n * fSc n := by
      apply tprod_congr
      intro n
      simp only [fS, fSc]
      split <;> simp_all
    _ = (∏' n, fS n) * ∏' n, fSc n := hmultS.tprod_mul hmultSc
    _ = (∏ n ∈ S, f n) * ∏' n, fSc n := by
      have ht : (∏' n, fS n) = ∏ n ∈ S, fS n := by
        apply tprod_eq_prod (s := S)
        intro n hn
        simp [fS, hn]
      simpa [fS] using congrArg (fun x => x * ∏' n, fSc n) ht

theorem hadamardRootProductAway_ne_zero
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (z : Complex) :
    hadamardRootProductAway (roots := roots)
      (hadamardVanishingIndices hsum z) z ≠ 0 := by
  let S := hadamardVanishingIndices hsum z
  let delta : Nat → Complex := fun n =>
    if n ∈ S then 0 else (roots n : Complex) * z ^ 2
  have hprod : (∏' n : Nat, ((1 : Complex) + delta n)) ≠ 0 := by
    apply tprod_one_add_ne_zero_of_summable
    · intro n hzero
      by_cases hn : n ∈ S
      · simp only [delta, if_pos hn, add_zero, one_ne_zero] at hzero
      · apply hn
        apply (mem_hadamardVanishingIndices hsum z n).mpr
        simpa only [delta, if_neg hn, hadamardRootFactor] using hzero
    · have hi := (summable_norm_hadamardRootFactor_sub_one hroots hsum z).indicator
        (S : Set Nat)ᶜ
      apply hi.congr
      intro n
      by_cases hn : n ∈ S <;>
        simp [delta, hn, Set.indicator]
  have heq :
      (∏' n : Nat, ((1 : Complex) + delta n)) =
        ∏' n : Nat, (if n ∈ S then 1 else hadamardRootFactor roots n z) := by
    apply tprod_congr
    intro n
    by_cases hn : n ∈ S
    · simp only [delta, if_pos hn, add_zero]
    · simp only [delta, if_neg hn, hadamardRootFactor]
  change (∏' n : Nat,
    (if n ∈ S then 1 else hadamardRootFactor roots n z)) ≠ 0
  rw [← heq]
  exact hprod


theorem analyticOrderAt_hadamardRootProduct_eq_card
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (z : Complex) :
    analyticOrderAt (hadamardRootProduct roots) z =
      (hadamardVanishingIndices hsum z).card := by
  let S := hadamardVanishingIndices hsum z
  let finitePart : Complex → Complex := fun w =>
    ∏ n ∈ S, hadamardRootFactor roots n w
  let awayPart : Complex → Complex :=
    hadamardRootProductAway (roots := roots) (hadamardVanishingIndices hsum z)
  have hfun : hadamardRootProduct roots = finitePart * awayPart := by
    funext w
    exact hadamardRootProduct_eq_finset_prod_mul_away hroots hsum S w
  have hfiniteAnalytic : AnalyticAt Complex finitePart z := by
    dsimp [finitePart]
    unfold hadamardRootFactor
    fun_prop
  have hawayAnalytic : AnalyticAt Complex awayPart z :=
    (analyticOnNhd_hadamardRootProductAway hroots hsum
      (hadamardVanishingIndices hsum z)) z (Set.mem_univ z)
  have hawayOrder : analyticOrderAt awayPart z = 0 :=
    hawayAnalytic.analyticOrderAt_eq_zero.mpr
      (hadamardRootProductAway_ne_zero hroots hsum z)
  have hpositive : ∀ n ∈ S, 0 < roots n := by
    intro n hn
    apply lt_of_le_of_ne (hroots n)
    intro hzero
    have hfactor : hadamardRootFactor roots n z = 0 := by
      simpa [S] using hn
    unfold hadamardRootFactor at hfactor
    rw [← hzero] at hfactor
    norm_num at hfactor
  rw [hfun, analyticOrderAt_mul hfiniteAnalytic hawayAnalytic, hawayOrder,
    add_zero]
  change analyticOrderAt (fun w =>
    ∏ n ∈ S, hadamardQuadraticFactor (roots n) w) z = (S.card : ENat)
  rw [analyticOrderAt_hadamardQuadraticFactor_prod S roots hpositive z]
  congr 1
  rw [Finset.filter_eq_self.mpr]
  intro n hn
  have hfactor : hadamardRootFactor roots n z = 0 := by
    simpa [S] using hn
  simpa [hadamardRootFactor, hadamardQuadraticFactor] using hfactor

end
end StatMech.FrontierA
