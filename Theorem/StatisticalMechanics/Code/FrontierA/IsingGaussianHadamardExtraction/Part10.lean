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
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part10
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem extractedHadamardRoots_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (n : Nat) :
    0 ≤ extractedHadamardRoots hF n := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  unfold extractedHadamardRoots encodedCountableSequence
  split
  · exact positiveImaginaryZeroMass_pos _ |>.le
  · rfl

theorem extractedHadamardRoots_encode
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (q : positiveImaginaryZeroCopies F) :
    extractedHadamardRoots hF
        (@Encodable.encode (positiveImaginaryZeroCopies F)
          (positiveImaginaryZeroCopiesEncodable hF) q) =
      positiveImaginaryZeroMass q := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  change encodedCountableSequence (positiveImaginaryZeroCopies F)
      positiveImaginaryZeroMass
        (@Encodable.encode (positiveImaginaryZeroCopies F)
          (positiveImaginaryZeroCopiesEncodable hF) q) = _
  have henc : positiveImaginaryZeroCopiesEncodable hF =
      Encodable.ofCountable (positiveImaginaryZeroCopies F) := rfl
  rw [henc]
  exact encodedCountableSequence_encode positiveImaginaryZeroMass q

theorem exists_positiveImaginaryZeroCopy_of_extractedHadamardRoots_ne_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (n : Nat) (hn : extractedHadamardRoots hF n ≠ 0) :
    ∃ q : positiveImaginaryZeroCopies F,
      @Encodable.encode (positiveImaginaryZeroCopies F)
        (positiveImaginaryZeroCopiesEncodable hF) q = n ∧
      extractedHadamardRoots hF n = positiveImaginaryZeroMass q := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  change encodedCountableSequence (positiveImaginaryZeroCopies F)
      positiveImaginaryZeroMass n ≠ 0 at hn
  obtain ⟨q, hqEncode, hqValue⟩ :=
    exists_encode_eq_of_encodedCountableSequence_ne_zero
      positiveImaginaryZeroMass n hn
  refine ⟨q, ?_, hqValue⟩
  exact hqEncode

theorem EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroMass_summable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    Summable (positiveImaginaryZeroMass (F := F)) := by
  let Q := {q : positiveImaginaryZeroCopies F // 1 ≤ q.1.1}
  let size : Q → Real := fun q => q.1.1.1
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  letI : Countable Q := inferInstance
  have hlarge : Summable (fun q : Q => 1 / size q ^ 2) := by
    apply summable_inverse_sq_of_linear_sublevel_count size
    · intro q
      exact q.2
    · intro R
      have hfinite := hF.positiveImaginaryZeroCopiesBelow_finite R
      apply hfinite.preimage Subtype.val_injective.injOn
    · exact hadamardZeroCountIntercept_nonneg hF
    · exact hadamardZeroCountSlope_nonneg hF
    · intro R hR
      let target := positiveImaginaryZeroCopiesBelow F R
      let source := {q : Q // size q ≤ R}
      letI : Finite target :=
        hF.positiveImaginaryZeroCopiesBelow_finite R |>.to_subtype
      let embed : source → target := fun q => ⟨q.1.1, q.2⟩
      have hinjective : Function.Injective embed := by
        intro q r h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : target => x.1) h
      have hcard : Nat.card source ≤ Nat.card target :=
        Nat.card_le_card_of_injective embed hinjective
      have hcardReal : (Nat.card source : Real) ≤
          (Nat.card target : Real) := by exact_mod_cast hcard
      exact hcardReal.trans
        (hF.card_positiveImaginaryZeroCopiesBelow_le_affine
          (lt_of_lt_of_le zero_lt_one hR))
  let large : Set (positiveImaginaryZeroCopies F) :=
    {q | 1 ≤ q.1.1}
  have hlargeIndicator : Summable
      (large.indicator (positiveImaginaryZeroMass (F := F))) := by
    apply summable_subtype_iff_indicator.mp
    simpa [Q, size, large, positiveImaginaryZeroMass, one_div] using hlarge
  have hsmallFinite : largeᶜ.Finite := by
    apply (hF.positiveImaginaryZeroCopiesBelow_finite 1).subset
    intro q hq
    change ¬1 ≤ q.1.1 at hq
    exact (lt_of_not_ge hq).le
  have hsmallIndicator : Summable
      (largeᶜ.indicator (positiveImaginaryZeroMass (F := F))) := by
    apply summable_of_finite_support
    exact hsmallFinite.subset Set.support_indicator_subset
  have hadd := hlargeIndicator.add hsmallIndicator
  apply hadd.congr
  intro q
  exact congrFun (Set.indicator_self_add_compl large
    (positiveImaginaryZeroMass (F := F))) q

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardRoots_summable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    Summable (extractedHadamardRoots hF) := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  change Summable (encodedCountableSequence
    (positiveImaginaryZeroCopies F) positiveImaginaryZeroMass)
  exact summable_encodedCountableSequence
    hF.positiveImaginaryZeroMass_summable


theorem EvenExponentialTypeImaginaryZeros.largeZero_logSlope_le
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 1 ≤ R) :
    ∑' q : {q : positiveImaginaryZeroCopies F // 1 ≤ q.1.1},
        2 * R / (q.1.1 ^ 2 + R ^ 2) ≤
      13 * hadamardZeroCountIntercept hF +
        18 * hadamardZeroCountSlope hF := by
  let Q := {q : positiveImaginaryZeroCopies F // 1 ≤ q.1.1}
  let size : Q → Real := fun q => q.1.1.1
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  letI : Countable Q := inferInstance
  apply tsum_two_mul_radius_div_sq_add_sq_le_of_linear_sublevel_count
    size (fun q => q.2)
  · intro S
    exact (hF.positiveImaginaryZeroCopiesBelow_finite S).preimage
      Subtype.val_injective.injOn
  · exact hadamardZeroCountIntercept_nonneg hF
  · exact hadamardZeroCountSlope_nonneg hF
  · intro S hS
    let target := positiveImaginaryZeroCopiesBelow F S
    let source := {q : Q // size q ≤ S}
    letI : Finite target :=
      hF.positiveImaginaryZeroCopiesBelow_finite S |>.to_subtype
    let embed : source → target := fun q => ⟨q.1.1, q.2⟩
    have hinjective : Function.Injective embed := by
      intro q r h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : target => x.1) h
    have hcard : Nat.card source ≤ Nat.card target :=
      Nat.card_le_card_of_injective embed hinjective
    have hcardReal : (Nat.card source : Real) ≤
        (Nat.card target : Real) := by exact_mod_cast hcard
    exact hcardReal.trans
      (hF.card_positiveImaginaryZeroCopiesBelow_le_affine
        (lt_of_lt_of_le zero_lt_one hS))
  · exact hR


end
end StatMech.FrontierA
