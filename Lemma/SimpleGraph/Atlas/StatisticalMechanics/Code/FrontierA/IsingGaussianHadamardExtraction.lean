import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part19
open Filter Metric StatMech StatMech.FrontierA


/--
[EvenExponentialTypeImaginaryZeros.entireZeroSet_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma entireZeroSet_countable_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  (entireZeroSet F).Countable := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.entireZeroSet_countable hF

/--
[EvenExponentialTypeImaginaryZeros.entireZeroSet_closed_discrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma entireZeroSet_closed_discrete_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  IsClosed (entireZeroSet F) ∧ IsDiscrete (entireZeroSet F) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.entireZeroSet_closed_discrete hF

/--
[EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroSet_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveImaginaryZeroSet_countable_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  (positiveImaginaryZeroSet F).Countable := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroSet_countable hF

/--
[EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroCopies_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveImaginaryZeroCopies_countable_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  Countable (positiveImaginaryZeroCopies F) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroCopies_countable hF

/--
[positiveImaginaryZeroMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveImaginaryZeroMass_pos_eq
  {F : Complex → Complex}
  {q : positiveImaginaryZeroCopies F} :
-- imply
  0 < positiveImaginaryZeroMass q := by
-- proof
  apply StatMech.FrontierA.positiveImaginaryZeroMass_pos q

/--
[EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroCopiesBelow_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveImaginaryZeroCopiesBelow_finite_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  (positiveImaginaryZeroCopiesBelow F R).Finite := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroCopiesBelow_finite hF R

/--
[EvenExponentialTypeImaginaryZeros.entireDiskZeroSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma entireDiskZeroSet_finite_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  Finite (entireDiskZeroSet F R) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.entireDiskZeroSet_finite hF R

/--
[EvenExponentialTypeImaginaryZeros.entireDiskZeroCopies_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma entireDiskZeroCopies_finite_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  Finite (entireDiskZeroCopies F R) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.entireDiskZeroCopies_finite hF R

/--
[EvenExponentialTypeImaginaryZeros.card_entireDiskZeroCopies_eq_finsum_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma card_entireDiskZeroCopies_eq_finsum_divisor_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  (Nat.card (entireDiskZeroCopies F R) : Int) = ∑ᶠ z : Complex, (MeromorphicOn.divisor F (closedBall 0 R)) z := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.card_entireDiskZeroCopies_eq_finsum_divisor hF R

/--
[EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma card_positiveImaginaryZeroCopiesBelow_le_divisor_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hR : 0 ≤ R) :
-- imply
  (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Int) ≤ ∑ᶠ z : Complex, (MeromorphicOn.divisor F (closedBall 0 R)) z := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_divisor hF hR

/--
[hadamardJensenMajorant_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardJensenMajorant_one_le_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  1 ≤ hadamardJensenMajorant hF R := by
-- proof
  apply StatMech.FrontierA.hadamardJensenMajorant_one_le hF R

/--
[EvenExponentialTypeImaginaryZeros.zeroMultiplicity_finsum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma zeroMultiplicity_finsum_le_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hR : 0 < R) :
-- imply
  ((∑ᶠ z : Complex, (MeromorphicOn.divisor F (closedBall 0 R)) z : Int) : Real) ≤ Real.log (hadamardJensenMajorant hF R / ‖F 0‖) / Real.log ((2 * R) / R) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.zeroMultiplicity_finsum_le hF hR

/--
[EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_jensen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma card_positiveImaginaryZeroCopiesBelow_le_jensen_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hR : 0 < R) :
-- imply
  (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤ Real.log (hadamardJensenMajorant hF R / ‖F 0‖) / Real.log ((2 * R) / R) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_jensen hF hR

/--
[hadamardZeroCountIntercept_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardZeroCountIntercept_nonneg_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  0 ≤ hadamardZeroCountIntercept hF := by
-- proof
  apply StatMech.FrontierA.hadamardZeroCountIntercept_nonneg hF

/--
[hadamardZeroCountSlope_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardZeroCountSlope_nonneg_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  0 ≤ hadamardZeroCountSlope hF := by
-- proof
  apply StatMech.FrontierA.hadamardZeroCountSlope_nonneg hF

/--
[EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma card_positiveImaginaryZeroCopiesBelow_le_affine_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hR : 0 < R) :
-- imply
  (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤ hadamardZeroCountIntercept hF + hadamardZeroCountSlope hF * R := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_affine hF hR

/--
[encodedCountableSequence_encode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma encodedCountableSequence_encode_eq
  [Countable α]
  {f : α → Real}
  {a : α} :
-- imply
  encodedCountableSequence α f (@Encodable.encode α (Encodable.ofCountable α) a) = f a := by
-- proof
  apply StatMech.FrontierA.encodedCountableSequence_encode f a

/--
[encodedCountableSequence_eq_zero_of_notMem_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma encodedCountableSequence_eq_zero_of_notMem_range_eq
  [Countable α]
  {f : α → Real}
  {n : Nat}
-- given
  (hn : n ∉ Set.range (@Encodable.encode α (Encodable.ofCountable α))) :
-- imply
  encodedCountableSequence α f n = 0 := by
-- proof
  apply StatMech.FrontierA.encodedCountableSequence_eq_zero_of_notMem_range f n hn

/--
[exists_encode_eq_of_encodedCountableSequence_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma exists_encode_eq_of_encodedCountableSequence_ne_zero_eq
  [Countable α]
  {f : α → Real}
  {n : Nat}
-- given
  (hn : encodedCountableSequence α f n ≠ 0) :
-- imply
  ∃ a : α, @Encodable.encode α (Encodable.ofCountable α) a = n ∧ encodedCountableSequence α f n = f a := by
-- proof
  apply StatMech.FrontierA.exists_encode_eq_of_encodedCountableSequence_ne_zero f n hn

/--
[summable_encodedCountableSequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma summable_encodedCountableSequence_eq
  [Countable α]
  {f : α → Real}
-- given
  (hf : Summable f) :
-- imply
  Summable (encodedCountableSequence α f) := by
-- proof
  apply StatMech.FrontierA.summable_encodedCountableSequence hf

/--
[tsum_encodedCountableSequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma tsum_encodedCountableSequence_eq
  [Countable α]
  {f : α → Real} :
-- imply
  ∑' n, encodedCountableSequence α f n = ∑' a, f a := by
-- proof
  apply StatMech.FrontierA.tsum_encodedCountableSequence f

/--
[extractedHadamardRoots_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardRoots_nonneg_eq
  {F : Complex → Complex}
  {n : Nat}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  0 ≤ extractedHadamardRoots hF n := by
-- proof
  apply StatMech.FrontierA.extractedHadamardRoots_nonneg hF n

/--
[extractedHadamardRoots_encode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardRoots_encode_eq
  {F : Complex → Complex}
  {q : positiveImaginaryZeroCopies F}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  extractedHadamardRoots hF (@Encodable.encode (positiveImaginaryZeroCopies F) (positiveImaginaryZeroCopiesEncodable hF) q) = positiveImaginaryZeroMass q := by
-- proof
  apply StatMech.FrontierA.extractedHadamardRoots_encode hF q

/--
[exists_positiveImaginaryZeroCopy_of_extractedHadamardRoots_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma exists_positiveImaginaryZeroCopy_of_extractedHadamardRoots_ne_zero_eq
  {F : Complex → Complex}
  {n : Nat}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hn : extractedHadamardRoots hF n ≠ 0) :
-- imply
  ∃ q : positiveImaginaryZeroCopies F, @Encodable.encode (positiveImaginaryZeroCopies F) (positiveImaginaryZeroCopiesEncodable hF) q = n ∧ extractedHadamardRoots hF n = positiveImaginaryZeroMass q := by
-- proof
  apply StatMech.FrontierA.exists_positiveImaginaryZeroCopy_of_extractedHadamardRoots_ne_zero hF n hn

/--
[EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroMass_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveImaginaryZeroMass_summable_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  Summable (positiveImaginaryZeroMass (F := F)) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroMass_summable hF

/--
[EvenExponentialTypeImaginaryZeros.extractedHadamardRoots_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardRoots_summable_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  Summable (extractedHadamardRoots hF) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.extractedHadamardRoots_summable hF

/--
[EvenExponentialTypeImaginaryZeros.largeZero_logSlope_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma largeZero_logSlope_le_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hR : 1 ≤ R) :
-- imply
  ∑' q : {q : positiveImaginaryZeroCopies F // 1 ≤ q.1.1}, 2 * R / (q.1.1 ^ 2 + R ^ 2) ≤ 13 * hadamardZeroCountIntercept hF + 18 * hadamardZeroCountSlope hF := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.largeZero_logSlope_le hF hR

/--
[EvenExponentialTypeImaginaryZeros.smallZeroLogSlopeBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma smallZeroLogSlopeBound_nonneg_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  0 ≤ smallZeroLogSlopeBound (F := F) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.smallZeroLogSlopeBound_nonneg hF

/--
[EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveZeroRadialLog_summable_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  Summable (fun q : positiveImaginaryZeroCopies F => Real.log (1 + R ^ 2 * positiveImaginaryZeroMass q)) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_summable hF R

/--
[EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveZeroRadialLog_hasDerivAt_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  HasDerivAt (positiveZeroRadialLog (F := F)) (∑' q : positiveImaginaryZeroCopies F, 2 * R / (q.1.1 ^ 2 + R ^ 2)) R := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_hasDerivAt hF R

/--
[EvenExponentialTypeImaginaryZeros.positiveZeroLogSlopeBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveZeroLogSlopeBound_nonneg_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  0 ≤ positiveZeroLogSlopeBound hF := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveZeroLogSlopeBound_nonneg hF

/--
[EvenExponentialTypeImaginaryZeros.positiveZero_logSlope_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveZero_logSlope_le_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hR : 1 ≤ R) :
-- imply
  (∑' q : positiveImaginaryZeroCopies F, 2 * R / (q.1.1 ^ 2 + R ^ 2)) ≤ positiveZeroLogSlopeBound hF := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveZero_logSlope_le hF hR

/--
[EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_le_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveZeroRadialLog_le_linear_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hR : 1 ≤ R) :
-- imply
  positiveZeroRadialLog (F := F) R ≤ positiveZeroRadialLog (F := F) 1 + positiveZeroLogSlopeBound hF * (R - 1) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_le_linear hF hR

/--
[EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_copies_tprod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardRootProduct_eq_copies_tprod_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  hadamardRootProduct (extractedHadamardRoots hF) z = ∏' q : positiveImaginaryZeroCopies F, (1 + (positiveImaginaryZeroMass q : Complex) * z ^ 2) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_copies_tprod hF z

/--
[EvenExponentialTypeImaginaryZeros.norm_hadamardRootProduct_le_radialLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma norm_hadamardRootProduct_le_radialLog_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  ‖hadamardRootProduct (extractedHadamardRoots hF) z‖ ≤ Real.exp (positiveZeroRadialLog (F := F) ‖z‖) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.norm_hadamardRootProduct_le_radialLog hF z

/--
[hadamardRootProductPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardRootProductPrefactor_pos_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  0 < hadamardRootProductPrefactor hF := by
-- proof
  apply StatMech.FrontierA.hadamardRootProductPrefactor_pos hF

/--
[EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_le_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma positiveZeroRadialLog_le_affine_eq
  {F : Complex → Complex}
  {R : Real}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hR : 0 ≤ R) :
-- imply
  positiveZeroRadialLog (F := F) R ≤ positiveZeroRadialLog (F := F) 1 + positiveZeroLogSlopeBound hF * R := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_le_affine hF R hR

/--
[EvenExponentialTypeImaginaryZeros.norm_hadamardRootProduct_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma norm_hadamardRootProduct_le_exp_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  ‖hadamardRootProduct (extractedHadamardRoots hF) z‖ ≤ hadamardRootProductPrefactor hF * Real.exp (positiveZeroLogSlopeBound hF * ‖z‖) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.norm_hadamardRootProduct_le_exp hF z

/--
[hasProdLocallyUniformlyOn_hadamardRootFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hasProdLocallyUniformlyOn_hadamardRootFactor_eq
  {roots : Nat → Real}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  HasProdLocallyUniformlyOn (hadamardRootFactor roots) (hadamardRootProduct roots) Set.univ := by
-- proof
  apply StatMech.FrontierA.hasProdLocallyUniformlyOn_hadamardRootFactor hroots hsum

/--
[analyticOnNhd_hadamardRootProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma analyticOnNhd_hadamardRootProduct_eq
  {roots : Nat → Real}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  AnalyticOnNhd Complex (hadamardRootProduct roots) Set.univ := by
-- proof
  apply StatMech.FrontierA.analyticOnNhd_hadamardRootProduct hroots hsum

/--
[hadamardVanishingIndices_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardVanishingIndices_finite_eq
  {roots : Nat → Real}
  {z : Complex}
-- given
  (hsum : Summable roots) :
-- imply
  {n | hadamardRootFactor roots n z = 0}.Finite := by
-- proof
  apply StatMech.FrontierA.hadamardVanishingIndices_finite hsum z

/--
[mem_hadamardVanishingIndices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma mem_hadamardVanishingIndices_eq
  {roots : Nat → Real}
  {z : Complex}
  {n : Nat}
-- given
  (hsum : Summable roots) :
-- imply
  n ∈ hadamardVanishingIndices hsum z ↔ hadamardRootFactor roots n z = 0 := by
-- proof
  apply StatMech.FrontierA.mem_hadamardVanishingIndices hsum z n

/--
[hasProdLocallyUniformlyOn_hadamardQuadraticFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hasProdLocallyUniformlyOn_hadamardQuadraticFactor_eq
  {r : ι → Real}
-- given
  (hr : ∀ i, 0 ≤ r i)
  (hsum : Summable r) :
-- imply
  HasProdLocallyUniformlyOn (fun i z => hadamardQuadraticFactor (r i) z) (fun z => ∏' i, hadamardQuadraticFactor (r i) z) Set.univ := by
-- proof
  apply StatMech.FrontierA.hasProdLocallyUniformlyOn_hadamardQuadraticFactor hr hsum

/--
[analyticOnNhd_hadamardRootProductAway](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma analyticOnNhd_hadamardRootProductAway_eq
  {roots : Nat → Real}
  {S : Finset Nat}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  AnalyticOnNhd Complex (hadamardRootProductAway (roots := roots) S) Set.univ := by
-- proof
  apply StatMech.FrontierA.analyticOnNhd_hadamardRootProductAway hroots hsum S

/--
[hadamardRootProduct_eq_finset_prod_mul_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardRootProduct_eq_finset_prod_mul_away_eq
  {roots : Nat → Real}
  {S : Finset Nat}
  {w : Complex}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  hadamardRootProduct roots w = (∏ n ∈ S, hadamardRootFactor roots n w) * hadamardRootProductAway (roots := roots) S w := by
-- proof
  apply StatMech.FrontierA.hadamardRootProduct_eq_finset_prod_mul_away hroots hsum S w

/--
[hadamardRootProductAway_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardRootProductAway_ne_zero_eq
  {roots : Nat → Real}
  {z : Complex}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  hadamardRootProductAway (roots := roots) (hadamardVanishingIndices hsum z) z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.hadamardRootProductAway_ne_zero hroots hsum z

/--
[analyticOrderAt_hadamardRootProduct_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma analyticOrderAt_hadamardRootProduct_eq_card_eq
  {roots : Nat → Real}
  {z : Complex}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  analyticOrderAt (hadamardRootProduct roots) z = (hadamardVanishingIndices hsum z).card := by
-- proof
  apply StatMech.FrontierA.analyticOrderAt_hadamardRootProduct_eq_card hroots hsum z

/--
[EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_zero_of_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardRootProduct_eq_zero_of_eq_zero_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hz : F z = 0) :
-- imply
  hadamardRootProduct (extractedHadamardRoots hF) z = 0 := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_zero_of_eq_zero hF hz

/--
[EvenExponentialTypeImaginaryZeros.eq_zero_of_hadamardRootProduct_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma eq_zero_of_hadamardRootProduct_eq_zero_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hz : hadamardRootProduct (extractedHadamardRoots hF) z = 0) :
-- imply
  F z = 0 := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.eq_zero_of_hadamardRootProduct_eq_zero hF hz

/--
[EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardRootProduct_eq_zero_iff_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  hadamardRootProduct (extractedHadamardRoots hF) z = 0 ↔ F z = 0 := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_zero_iff hF z

/--
[EvenExponentialTypeImaginaryZeros.card_hadamardVanishingIndices_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma card_hadamardVanishingIndices_positive_eq
  {F : Complex → Complex}
  {y : positiveImaginaryZeroSet F}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  (hadamardVanishingIndices hF.extractedHadamardRoots_summable ((y.1 : Complex) * Complex.I)).card = analyticOrderNatAt F ((y.1 : Complex) * Complex.I) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.card_hadamardVanishingIndices_positive hF y

/--
[hadamardRootProduct_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma hadamardRootProduct_neg_eq
  {roots : Nat → Real}
  {z : Complex} :
-- imply
  hadamardRootProduct roots (-z) = hadamardRootProduct roots z := by
-- proof
  apply StatMech.FrontierA.hadamardRootProduct_neg roots z

/--
[EvenExponentialTypeImaginaryZeros.analyticOrderAt_hadamardRootProduct_eq_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma analyticOrderAt_hadamardRootProduct_eq_positive_eq
  {F : Complex → Complex}
  {y : positiveImaginaryZeroSet F}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) ((y.1 : Complex) * Complex.I) = analyticOrderAt F ((y.1 : Complex) * Complex.I) := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.analyticOrderAt_hadamardRootProduct_eq_positive hF y

/--
[EvenExponentialTypeImaginaryZeros.analyticOrderAt_hadamardRootProduct_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma analyticOrderAt_hadamardRootProduct_eq_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) z = analyticOrderAt F z := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.analyticOrderAt_hadamardRootProduct_eq hF z

/--
[EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_analytic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardQuotient_analytic_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  AnalyticAt Complex (extractedHadamardQuotient hF) z := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_analytic hF z

/--
[EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardQuotient_ne_zero_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  extractedHadamardQuotient hF z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_ne_zero hF z

/--
[EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardQuotient_mul_eq_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  extractedHadamardQuotient hF z * hadamardRootProduct (extractedHadamardRoots hF) z = F z := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_mul_eq hF z

/--
[EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardQuotient_even_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  extractedHadamardQuotient hF (-z) = extractedHadamardQuotient hF z := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_even hF z

/--
[EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardQuotient_zero_eq
  {F : Complex → Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  extractedHadamardQuotient hF 0 = F 0 := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_zero hF

/--
[EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_eq_zeroValue_of_growth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardQuotient_eq_zeroValue_of_growth_eq
  {F : Complex → Complex}
  {A B : Real}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F)
  (hA : 0 < A)
  (hB : 0 ≤ B)
  (hgrowth : ∀ z, ‖extractedHadamardQuotient hF z‖ ≤ A * Real.exp (B * ‖z‖)) :
-- imply
  extractedHadamardQuotient hF z = F 0 := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_eq_zeroValue_of_growth hF hA hB hgrowth z

/--
[EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_eq_zeroValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean)
-/
@[path]
private lemma extractedHadamardQuotient_eq_zeroValue_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenExponentialTypeImaginaryZeros F) :
-- imply
  extractedHadamardQuotient hF z = F 0 := by
-- proof
  apply StatMech.FrontierA.EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_eq_zeroValue hF z


-- created on 2026-10-23
