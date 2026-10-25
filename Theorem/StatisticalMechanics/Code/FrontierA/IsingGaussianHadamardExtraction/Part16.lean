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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part16
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem inverseSq_mul_imaginary_sq
    (y : Real) (hy : 0 < y) :
    1 + ((((y ^ 2)⁻¹ : Real) : Complex)) *
      (((y : Complex) * Complex.I) ^ 2) = 0 := by
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring_nf
  rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hy.ne')]
  ring

theorem hadamardQuadraticFactor_imaginary_eq_zero_iff
    (y r : Real) (hy : 0 < y) :
    hadamardQuadraticFactor r ((y : Complex) * Complex.I) = 0 ↔
      r = (y ^ 2)⁻¹ := by
  constructor
  · intro h
    unfold hadamardQuadraticFactor at h
    rw [mul_pow, Complex.I_sq] at h
    ring_nf at h
    norm_cast at h
    rw [inv_eq_one_div, eq_div_iff (pow_ne_zero 2 hy.ne')]
    nlinarith [h]
  · intro h
    rw [h]
    exact inverseSq_mul_imaginary_sq y hy

theorem eq_pos_or_neg_imaginary_of_inverseSq_factor_zero
    (y : Real) (hy : 0 < y) (z : Complex)
    (hzero : 1 + ((((y ^ 2)⁻¹ : Real) : Complex)) * z ^ 2 = 0) :
    z = (y : Complex) * Complex.I ∨
      z = -((y : Complex) * Complex.I) := by
  have hy0 : (y : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hpoly :
      (z - (y : Complex) * Complex.I) *
        (z + (y : Complex) * Complex.I) = 0 := by
    push_cast at hzero
    field_simp at hzero
    simp at hzero
    calc
      (z - (y : Complex) * Complex.I) *
          (z + (y : Complex) * Complex.I) =
          z ^ 2 - (y : Complex) ^ 2 * Complex.I ^ 2 := by ring
      _ = z ^ 2 + (y : Complex) ^ 2 := by
        rw [Complex.I_sq]
        ring
      _ = 0 := by simpa [add_comm] using hzero
  rcases mul_eq_zero.mp hpoly with hpos | hneg
  · exact Or.inl (sub_eq_zero.mp hpos)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hneg)

theorem EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_zero_of_eq_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {z : Complex} (hz : F z = 0) :
    hadamardRootProduct (extractedHadamardRoots hF) z = 0 := by
  have hre : z.re = 0 := hF.zeros_imaginary z hz
  have hzform : z = (z.im : Complex) * Complex.I := by
    apply Complex.ext
    · simpa [hre]
    · simp
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hF.value_zero_ne hz
  have him0 : z.im ≠ 0 := by
    intro him
    apply hz0
    rw [hzform, him]
    simp
  by_cases himpos : 0 < z.im
  · let q := hF.positiveZeroCopy himpos (by simpa [← hzform] using hz)
    let n : Nat := @Encodable.encode (positiveImaginaryZeroCopies F)
      (positiveImaginaryZeroCopiesEncodable hF) q
    apply tprod_of_exists_eq_zero
    refine ⟨n, ?_⟩
    unfold hadamardRootFactor
    rw [extractedHadamardRoots_encode hF q]
    change 1 + ((((z.im ^ 2)⁻¹ : Real) : Complex)) * z ^ 2 = 0
    have hzsq : z ^ 2 = (((z.im : Complex) * Complex.I) ^ 2) :=
      congrArg (fun w : Complex => w ^ 2) hzform
    rw [hzsq]
    exact inverseSq_mul_imaginary_sq z.im himpos
  · have himneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt himpos) him0
    let y : Real := -z.im
    have hy : 0 < y := neg_pos.mpr himneg
    have hyz : (y : Complex) * Complex.I = -z := by
      rw [hzform]
      dsimp [y]
      push_cast
      ring
    have hyzero : F ((y : Complex) * Complex.I) = 0 := by
      rw [hyz, hF.even, hz]
    let q := hF.positiveZeroCopy hy hyzero
    let n : Nat := @Encodable.encode (positiveImaginaryZeroCopies F)
      (positiveImaginaryZeroCopiesEncodable hF) q
    apply tprod_of_exists_eq_zero
    refine ⟨n, ?_⟩
    unfold hadamardRootFactor
    rw [extractedHadamardRoots_encode hF q]
    change 1 + ((((y ^ 2)⁻¹ : Real) : Complex)) * z ^ 2 = 0
    have hzneg : z = -((y : Complex) * Complex.I) := by
      rw [hzform]
      dsimp [y]
      push_cast
      ring
    have hzsq : z ^ 2 = (((y : Complex) * Complex.I) ^ 2) := by
      rw [hzneg]
      ring
    rw [hzsq]
    exact inverseSq_mul_imaginary_sq y hy

theorem EvenExponentialTypeImaginaryZeros.eq_zero_of_hadamardRootProduct_eq_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {z : Complex} (hz : hadamardRootProduct (extractedHadamardRoots hF) z = 0) :
    F z = 0 := by
  have hfactor : ∃ n,
      hadamardRootFactor (extractedHadamardRoots hF) n z = 0 := by
    by_contra hnone
    have hall : ∀ n,
        1 + (extractedHadamardRoots hF n : Complex) * z ^ 2 ≠ 0 := by
      intro n hn
      exact hnone ⟨n, hn⟩
    have hnonzero : hadamardRootProduct (extractedHadamardRoots hF) z ≠ 0 := by
      unfold hadamardRootProduct hadamardRootFactor
      apply tprod_one_add_ne_zero_of_summable hall
      exact summable_norm_hadamardRootFactor_sub_one
        (extractedHadamardRoots_nonneg hF)
        hF.extractedHadamardRoots_summable z
    exact hnonzero hz
  obtain ⟨n, hn⟩ := hfactor
  have hroot : extractedHadamardRoots hF n ≠ 0 := by
    intro hzero
    simp [hadamardRootFactor, hzero] at hn
  obtain ⟨q, _hqEncode, hqValue⟩ :=
    exists_positiveImaginaryZeroCopy_of_extractedHadamardRoots_ne_zero
      hF n hroot
  let y : Real := q.1.1
  have hy : 0 < y := q.1.2.1
  have hfactorEq :
      1 + (((y ^ 2)⁻¹ : Real) : Complex) * z ^ 2 = 0 := by
    unfold hadamardRootFactor at hn
    rw [hqValue] at hn
    simpa [positiveImaginaryZeroMass, y] using hn
  rcases eq_pos_or_neg_imaginary_of_inverseSq_factor_zero y hy z hfactorEq with
    hzloc | hzloc
  ·
    rw [hzloc]
    exact q.1.2.2
  ·
    rw [hzloc, hF.even]
    exact q.1.2.2

theorem EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_zero_iff
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    hadamardRootProduct (extractedHadamardRoots hF) z = 0 ↔ F z = 0 :=
  ⟨hF.eq_zero_of_hadamardRootProduct_eq_zero,
    hF.hadamardRootProduct_eq_zero_of_eq_zero⟩


theorem EvenExponentialTypeImaginaryZeros.card_hadamardVanishingIndices_positive
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (y : positiveImaginaryZeroSet F) :
    (hadamardVanishingIndices hF.extractedHadamardRoots_summable
      ((y.1 : Complex) * Complex.I)).card =
      analyticOrderNatAt F ((y.1 : Complex) * Complex.I) := by
  let roots := extractedHadamardRoots hF
  let hsum := hF.extractedHadamardRoots_summable
  let z : Complex := (y.1 : Complex) * Complex.I
  let S := hadamardVanishingIndices hsum z
  let encodeAt : Fin (analyticOrderNatAt F z) → Nat := fun i =>
    @Encodable.encode (positiveImaginaryZeroCopies F)
      (positiveImaginaryZeroCopiesEncodable hF) ⟨y, i⟩
  have hfactorIff (n : Nat) :
      hadamardRootFactor roots n z = 0 ↔ roots n = (y.1 ^ 2)⁻¹ := by
    simpa [roots, z, hadamardRootFactor, hadamardQuadraticFactor] using
      hadamardQuadraticFactor_imaginary_eq_zero_iff
        y.1 (roots n) y.2.1
  have hS : S = Finset.univ.image encodeAt := by
    apply Finset.ext
    intro n
    rw [Finset.mem_image]
    constructor
    · intro hn
      have hfactor : hadamardRootFactor roots n z = 0 := by
        exact (mem_hadamardVanishingIndices hsum z n).mp (by simpa [S] using hn)
      have hrootValue : roots n = (y.1 ^ 2)⁻¹ := (hfactorIff n).mp hfactor
      have hrootNe : roots n ≠ 0 := by
        rw [hrootValue]
        exact inv_ne_zero (pow_ne_zero 2 y.2.1.ne')
      obtain ⟨q, hqEncode, hqValue⟩ :=
        exists_positiveImaginaryZeroCopy_of_extractedHadamardRoots_ne_zero
          hF n (by simpa [roots] using hrootNe)
      have hmass : (q.1.1 ^ 2)⁻¹ = (y.1 ^ 2)⁻¹ := by
        calc
          (q.1.1 ^ 2)⁻¹ = positiveImaginaryZeroMass q := rfl
          _ = roots n := by simpa [roots] using hqValue.symm
          _ = (y.1 ^ 2)⁻¹ := hrootValue
      have hsq : q.1.1 ^ 2 = y.1 ^ 2 := by
        have := congrArg (fun x : Real => x⁻¹) hmass
        simpa using this
      have hy : q.1.1 = y.1 := by
        nlinarith [q.1.2.1, y.2.1]
      have hqLocation : q.1 = y := Subtype.ext hy
      cases q with
      | mk qy qi =>
          dsimp at hqLocation hqEncode hqValue ⊢
          subst qy
          exact ⟨qi, Finset.mem_univ _, by simpa [encodeAt, z] using hqEncode⟩
    · rintro ⟨i, _hi, rfl⟩
      have hroot := extractedHadamardRoots_encode hF
        (⟨y, i⟩ : positiveImaginaryZeroCopies F)
      apply (mem_hadamardVanishingIndices hsum z _).mpr
      apply (hfactorIff _).mpr
      simpa [roots, positiveImaginaryZeroMass] using hroot
  have hencodeAt : Function.Injective encodeAt := by
    intro i j hij
    have hq : (⟨y, i⟩ : positiveImaginaryZeroCopies F) = ⟨y, j⟩ :=
      @Encodable.encode_injective (positiveImaginaryZeroCopies F)
        (positiveImaginaryZeroCopiesEncodable hF) _ _
          (by simpa [encodeAt] using hij)
    apply Fin.ext
    exact congrArg (fun q : positiveImaginaryZeroCopies F => q.2.1) hq
  change S.card = analyticOrderNatAt F z
  rw [hS, Finset.card_image_of_injective _ hencodeAt]
  simp

theorem analyticOrderAt_neg_eq_of_even
    {f : Complex → Complex} (hf : ∀ z, AnalyticAt Complex f z)
    (heven : ∀ z, f (-z) = f z) (z : Complex) :
    analyticOrderAt f (-z) = analyticOrderAt f z := by
  let neg : Complex → Complex := fun w => -w
  have hnegAnalytic : AnalyticAt Complex neg z := by
    dsimp [neg]
    fun_prop
  have hnegDeriv : deriv neg z ≠ 0 := by
    have hderiv := (hasDerivAt_id z).neg.deriv
    simpa [neg] using hderiv
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) hnegAnalytic hnegDeriv
  have hfun : f ∘ neg = f := by
    funext w
    exact heven w
  rw [hfun] at hcomp
  simpa [neg] using hcomp.symm

theorem hadamardRootProduct_neg (roots : Nat → Real) (z : Complex) :
    hadamardRootProduct roots (-z) = hadamardRootProduct roots z := by
  unfold hadamardRootProduct
  apply tprod_congr
  intro n
  unfold hadamardRootFactor
  ring

theorem EvenExponentialTypeImaginaryZeros.analyticOrderAt_hadamardRootProduct_eq_positive
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (y : positiveImaginaryZeroSet F) :
    analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF))
        ((y.1 : Complex) * Complex.I) =
      analyticOrderAt F ((y.1 : Complex) * Complex.I) := by
  rw [analyticOrderAt_hadamardRootProduct_eq_card
    (extractedHadamardRoots_nonneg hF)
    hF.extractedHadamardRoots_summable]
  rw [hF.card_hadamardVanishingIndices_positive y]
  exact Nat.cast_analyticOrderNatAt
    (hF.analyticOrderAt_ne_top ((y.1 : Complex) * Complex.I))


theorem EvenExponentialTypeImaginaryZeros.analyticOrderAt_hadamardRootProduct_eq
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) z =
      analyticOrderAt F z := by
  by_cases hz : F z = 0
  · have hre : z.re = 0 := hF.zeros_imaginary z hz
    have hzform : z = (z.im : Complex) * Complex.I := by
      apply Complex.ext
      · simpa [hre]
      · simp
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      exact hF.value_zero_ne hz
    have him0 : z.im ≠ 0 := by
      intro him
      apply hz0
      rw [hzform, him]
      simp
    by_cases himpos : 0 < z.im
    · let y : positiveImaginaryZeroSet F :=
        ⟨z.im, himpos, by simpa [← hzform] using hz⟩
      simpa [y, ← hzform] using
        hF.analyticOrderAt_hadamardRootProduct_eq_positive y
    · have himneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt himpos) him0
      let yval : Real := -z.im
      have hypos : 0 < yval := neg_pos.mpr himneg
      have hyz : (yval : Complex) * Complex.I = -z := by
        rw [hzform]
        dsimp [yval]
        push_cast
        ring
      have hyzero : F ((yval : Complex) * Complex.I) = 0 := by
        rw [hyz, hF.even, hz]
      let y : positiveImaginaryZeroSet F := ⟨yval, hypos, hyzero⟩
      have hpositive := hF.analyticOrderAt_hadamardRootProduct_eq_positive y
      have hprodEvenOrder := analyticOrderAt_neg_eq_of_even
        (fun w => (analyticOnNhd_hadamardRootProduct
          (extractedHadamardRoots_nonneg hF)
          hF.extractedHadamardRoots_summable) w (Set.mem_univ w))
        (hadamardRootProduct_neg (extractedHadamardRoots hF)) z
      have hFEvenOrder := analyticOrderAt_neg_eq_of_even
        (fun w => hF.analytic w (Set.mem_univ w)) hF.even z
      calc
        analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) z =
            analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) (-z) :=
          hprodEvenOrder.symm
        _ = analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF))
            ((y.1 : Complex) * Complex.I) := by rw [hyz]
        _ = analyticOrderAt F ((y.1 : Complex) * Complex.I) := hpositive
        _ = analyticOrderAt F (-z) := by rw [hyz]
        _ = analyticOrderAt F z := hFEvenOrder
  · have hprodNe :
        hadamardRootProduct (extractedHadamardRoots hF) z ≠ 0 := by
      intro hzero
      exact hz ((hF.hadamardRootProduct_eq_zero_iff z).mp hzero)
    rw [(analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr
        hprodNe,
      (hF.analytic z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr hz]


end
end StatMech.FrontierA
