import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
open StatMech StatMech.Exact3D StatMech.Exact3D.TailSummability StatMech.Exact3D.TailSummability.InfiniteTailCertificate StatMech.Exact3D.TailSummability.FiniteSupportCertificate StatMech.Exact3D.ContributionSplit


/--
[summable_prefixWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma summable_prefixWeight_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  Summable C.prefixWeight := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.summable_prefixWeight C

/--
[tsum_prefixWeight_eq_prefixWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_prefixWeight_eq_prefixWeight_sum_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  (∑' a, C.prefixWeight a) = ∑ a ∈ C.finitePrefix, C.prefixWeight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.tsum_prefixWeight_eq_prefixWeight_sum C

/--
[prefixWeight_sum_eq_prefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma prefixWeight_sum_eq_prefixSum_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  (∑ a ∈ C.finitePrefix, C.prefixWeight a) = C.prefixSum := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.prefixWeight_sum_eq_prefixSum C

/--
[tsum_prefixWeight_eq_prefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_prefixWeight_eq_prefixSum_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  (∑' a, C.prefixWeight a) = C.prefixSum := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.tsum_prefixWeight_eq_prefixSum C

/--
[summable_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma summable_weight_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  Summable C.weight := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.summable_weight C

/--
[tsum_weight_eq_prefixSum_add_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_weight_eq_prefixSum_add_tail_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  (∑' a, C.weight a) = C.prefixSum + ∑' a, C.tailWeight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.tsum_weight_eq_prefixSum_add_tail C

/--
[tsum_weight_le_prefixSum_add_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_weight_le_prefixSum_add_tailBound_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  (∑' a, C.weight a) ≤ C.prefixSum + C.tailBound := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.tsum_weight_le_prefixSum_add_tailBound C

/--
[tsum_weight_le_prefixSum_add_of_tailBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_weight_le_prefixSum_add_of_tailBound_le_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (∑' a, C.weight a) ≤ C.prefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.tsum_weight_le_prefixSum_add_of_tailBound_le C hle

/--
[prefixSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma prefixSum_nonneg_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  0 ≤ C.prefixSum := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.prefixSum_nonneg C

/--
[tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tail_tsum_nonneg_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  0 ≤ ∑' a, C.tailWeight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.tail_tsum_nonneg C

/--
[tsum_weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_weight_nonneg_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  0 ≤ ∑' a, C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.tsum_weight_nonneg C

/--
[tailBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tailBound_nonneg_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α} :
-- imply
  0 ≤ C.tailBound := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.tailBound_nonneg C

/--
[weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma weight_nonneg_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {a : α} :
-- imply
  0 ≤ C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.weight_nonneg C a

/--
[with_larger_tailBound_finitePrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma with_larger_tailBound_finitePrefix_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).finitePrefix = C.finitePrefix := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.with_larger_tailBound_finitePrefix C hle

/--
[with_larger_tailBound_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma with_larger_tailBound_weight_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).weight = C.weight := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.with_larger_tailBound_weight C hle

/--
[with_larger_tailBound_prefixWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma with_larger_tailBound_prefixWeight_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).prefixWeight = C.prefixWeight := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.with_larger_tailBound_prefixWeight C hle

/--
[with_larger_tailBound_tailWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma with_larger_tailBound_tailWeight_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).tailWeight = C.tailWeight := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.with_larger_tailBound_tailWeight C hle

/--
[with_larger_tailBound_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma with_larger_tailBound_tailBound_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).tailBound = tailBound' := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.with_larger_tailBound_tailBound C hle

/--
[with_larger_tailBound_prefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma with_larger_tailBound_prefixSum_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).prefixSum = C.prefixSum := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.with_larger_tailBound_prefixSum C hle

/--
[of_masked_tailEnvelope_finitePrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma of_masked_tailEnvelope_finitePrefix_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {finitePrefix : Finset α}
  {weight tailEnvelope : α → ℝ}
  {tailBound : ℝ}
-- given
  (hweight_nonneg : ∀ a, 0 ≤ weight a)
  (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
  (hweight_le_tailEnvelope : ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
  (hsummable_masked : Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
  (hmasked_tsum_le : (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤ tailBound) :
-- imply
  (of_masked_tailEnvelope finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked hmasked_tsum_le).finitePrefix = finitePrefix := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope_finitePrefix C finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[of_masked_tailEnvelope_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma of_masked_tailEnvelope_weight_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {finitePrefix : Finset α}
  {weight tailEnvelope : α → ℝ}
  {tailBound : ℝ}
-- given
  (hweight_nonneg : ∀ a, 0 ≤ weight a)
  (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
  (hweight_le_tailEnvelope : ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
  (hsummable_masked : Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
  (hmasked_tsum_le : (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤ tailBound) :
-- imply
  (of_masked_tailEnvelope finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked hmasked_tsum_le).weight = weight := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope_weight C finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[of_masked_tailEnvelope_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma of_masked_tailEnvelope_tailBound_eq
  [DecidableEq α]
  {C : InfiniteTailCertificate α}
  {finitePrefix : Finset α}
  {weight tailEnvelope : α → ℝ}
  {tailBound : ℝ}
-- given
  (hweight_nonneg : ∀ a, 0 ≤ weight a)
  (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
  (hweight_le_tailEnvelope : ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
  (hsummable_masked : Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
  (hmasked_tsum_le : (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤ tailBound) :
-- imply
  (of_masked_tailEnvelope finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked hmasked_tsum_le).tailBound = tailBound := by
-- proof
  apply StatMech.Exact3D.TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope_tailBound C finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg_off hweight_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[toInfiniteTailCertificate_finitePrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma toInfiniteTailCertificate_finitePrefix_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  C.toInfiniteTailCertificate.finitePrefix = C.finitePrefix := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.toInfiniteTailCertificate_finitePrefix C

/--
[toInfiniteTailCertificate_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma toInfiniteTailCertificate_weight_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  C.toInfiniteTailCertificate.weight = C.weight := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.toInfiniteTailCertificate_weight C

/--
[toInfiniteTailCertificate_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma toInfiniteTailCertificate_tailBound_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  C.toInfiniteTailCertificate.tailBound = C.tailBound := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.toInfiniteTailCertificate_tailBound C

/--
[toInfiniteTailCertificate_tsum_weight_le_prefix_add_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma toInfiniteTailCertificate_tsum_weight_le_prefix_add_tailBound_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  (∑' a, C.toInfiniteTailCertificate.weight a) ≤ C.toInfiniteTailCertificate.prefixSum + C.tailBound := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.toInfiniteTailCertificate_tsum_weight_le_prefix_add_tailBound C

/--
[tsum_total_le_prefixSum_add_tailBound_of_tailEnvelope_off_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_total_le_prefixSum_add_tailBound_of_tailEnvelope_off_prefix_eq
  [DecidableEq α]
  {S : ContributionSplit α}
  {finitePrefix : Finset α}
  {tailEnvelope : α → ℝ}
  {tailBound : ℝ}
-- given
  (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
  (hadd : S.Additive)
  (hfinite_zero_off_prefix : ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
  (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
  (htail_le_tailEnvelope : ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
  (hsummable_tailEnvelope : Summable tailEnvelope)
  (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (S.infiniteTailCertificate_of_tailEnvelope_off_prefix finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope htailEnvelope_tsum_le).prefixSum + tailBound := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.tsum_total_le_prefixSum_add_tailBound_of_tailEnvelope_off_prefix S finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope htailEnvelope_tsum_le

/--
[tsum_total_le_prefixSum_add_tailBound_of_masked_tailEnvelope_off_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_total_le_prefixSum_add_tailBound_of_masked_tailEnvelope_off_prefix_eq
  [DecidableEq α]
  {S : ContributionSplit α}
  {finitePrefix : Finset α}
  {tailEnvelope : α → ℝ}
  {tailBound : ℝ}
-- given
  (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
  (hadd : S.Additive)
  (hfinite_zero_off_prefix : ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
  (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
  (htail_le_tailEnvelope : ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
  (hsummable_masked : Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
  (hmasked_tsum_le : (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (S.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).prefixSum + tailBound := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.tsum_total_le_prefixSum_add_tailBound_of_masked_tailEnvelope_off_prefix S finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_tailBound_eq
  [DecidableEq α]
  {S : ContributionSplit β}
  {finitePrefix : Finset β}
  [DecidableEq Case]
  {T : RatInterval.CaseTable Case}
  {classify : β → Case}
  {finiteBound prefixTailBound tailBound : ℝ}
  {tailEnvelope : β → ℝ}
-- given
  (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
  (hadd : S.Additive)
  (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
  (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
  (htailPrefixSum_le : (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
  (hfinite_zero_off_prefix : ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
  (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
  (htail_le_tailEnvelope : ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
  (hsummable_tailEnvelope : Summable tailEnvelope)
  (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (finitePrefix.card : ℝ) * finiteBound + prefixTailBound + tailBound := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_tailBound S finitePrefix tailEnvelope htotal_nonneg hadd hfinite htail_on_prefix htailPrefixSum_le hfinite_zero_off_prefix henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope htailEnvelope_tsum_le

/--
[tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_maskedTailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean)
-/
@[path]
private lemma tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_maskedTailBound_eq
  [DecidableEq α]
  {S : ContributionSplit β}
  {finitePrefix : Finset β}
  [DecidableEq β]
  [DecidableEq Case]
  {T : RatInterval.CaseTable Case}
  {classify : β → Case}
  {finiteBound prefixTailBound tailBound : ℝ}
  {tailEnvelope : β → ℝ}
-- given
  (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
  (hadd : S.Additive)
  (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
  (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
  (htailPrefixSum_le : (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
  (hfinite_zero_off_prefix : ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
  (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
  (htail_le_tailEnvelope : ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
  (hsummable_masked : Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
  (hmasked_tsum_le : (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (finitePrefix.card : ℝ) * finiteBound + prefixTailBound + tailBound := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_maskedTailBound S finitePrefix tailEnvelope htotal_nonneg hadd hfinite htail_on_prefix htailPrefixSum_le hfinite_zero_off_prefix henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le


-- created on 2026-10-23
