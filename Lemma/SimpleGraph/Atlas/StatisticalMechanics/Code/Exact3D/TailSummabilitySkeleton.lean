import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
open StatMech StatMech.Exact3D StatMech.Exact3D.TailSummability StatMech.Exact3D.TailSummability.FiniteSupportCertificate StatMech.Exact3D.ContributionSplit


/--
[sum_nonneg_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma sum_nonneg_on_eq
  {s : Finset α}
  {f : α → ℝ}
-- given
  (hf : ∀ a, a ∈ s → 0 ≤ f a) :
-- imply
  0 ≤ ∑ a ∈ s, f a := by
-- proof
  apply StatMech.Exact3D.TailSummability.sum_nonneg_on hf

/--
[sum_eq_prefix_add_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma sum_eq_prefix_add_tail_eq
  [DecidableEq α]
  {s front : Finset α}
  {f : α → ℝ}
-- given
  (hfront : front ⊆ s) :
-- imply
  (∑ a ∈ s, f a) = (∑ a ∈ front, f a) + ∑ a ∈ s \ front, f a := by
-- proof
  apply StatMech.Exact3D.TailSummability.sum_eq_prefix_add_tail hfront f

/--
[tail_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tail_sum_nonneg_eq
  [DecidableEq α]
  {s front : Finset α}
  {f : α → ℝ}
-- given
  (hf : ∀ a, a ∈ s → a ∉ front → 0 ≤ f a) :
-- imply
  0 ≤ ∑ a ∈ s \ front, f a := by
-- proof
  apply StatMech.Exact3D.TailSummability.tail_sum_nonneg hf

/--
[tail_sum_le_envelope_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tail_sum_le_envelope_sum_eq
  [DecidableEq α]
  {s front : Finset α}
  {f envelope : α → ℝ}
-- given
  (henv : ∀ a, a ∈ s → a ∉ front → f a ≤ envelope a) :
-- imply
  (∑ a ∈ s \ front, f a) ≤ ∑ a ∈ s \ front, envelope a := by
-- proof
  apply StatMech.Exact3D.TailSummability.tail_sum_le_envelope_sum henv

/--
[mem_tailSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma mem_tailSupport_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {a : α} :
-- imply
  a ∈ C.tailSupport ↔ a ∈ C.support ∧ a ∉ C.finitePrefix := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.mem_tailSupport C

/--
[summable_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma summable_weight_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  Summable C.weight := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.summable_weight C

/--
[hasSum_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma hasSum_weight_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  HasSum C.weight (∑ a ∈ C.support, C.weight a) := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.hasSum_weight C

/--
[tsum_eq_support_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tsum_eq_support_sum_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  (∑' a, C.weight a) = ∑ a ∈ C.support, C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tsum_eq_support_sum C

/--
[support_sum_eq_prefix_add_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma support_sum_eq_prefix_add_tail_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  (∑ a ∈ C.support, C.weight a) = (∑ a ∈ C.finitePrefix, C.weight a) + ∑ a ∈ C.tailSupport, C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.support_sum_eq_prefix_add_tail C

/--
[tsum_eq_prefix_add_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tsum_eq_prefix_add_tail_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  (∑' a, C.weight a) = (∑ a ∈ C.finitePrefix, C.weight a) + ∑ a ∈ C.tailSupport, C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tsum_eq_prefix_add_tail C

/--
[prefix_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma prefix_sum_nonneg_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  0 ≤ ∑ a ∈ C.finitePrefix, C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.prefix_sum_nonneg C

/--
[tail_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tail_sum_nonneg_eq_2
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  0 ≤ ∑ a ∈ C.tailSupport, C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tail_sum_nonneg C

/--
[tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tsum_nonneg_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  0 ≤ ∑' a, C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tsum_nonneg C

/--
[envelope_tail_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma envelope_tail_sum_nonneg_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  0 ≤ ∑ a ∈ C.tailSupport, C.envelope a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.envelope_tail_sum_nonneg C

/--
[tail_sum_le_envelope_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tail_sum_le_envelope_sum_eq_2
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  (∑ a ∈ C.tailSupport, C.weight a) ≤ ∑ a ∈ C.tailSupport, C.envelope a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tail_sum_le_envelope_sum C

/--
[tail_sum_le_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tail_sum_le_bound_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  (∑ a ∈ C.tailSupport, C.weight a) ≤ C.tailBound := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tail_sum_le_bound C

/--
[tailBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tailBound_nonneg_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  0 ≤ C.tailBound := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tailBound_nonneg C

/--
[with_larger_tailBound_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_larger_tailBound_support_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).support = C.support := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_larger_tailBound_support C hle

/--
[with_larger_tailBound_finitePrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_larger_tailBound_finitePrefix_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).finitePrefix = C.finitePrefix := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_larger_tailBound_finitePrefix C hle

/--
[with_larger_tailBound_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_larger_tailBound_weight_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).weight = C.weight := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_larger_tailBound_weight C hle

/--
[with_larger_tailBound_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_larger_tailBound_envelope_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).envelope = C.envelope := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_larger_tailBound_envelope C hle

/--
[with_larger_tailBound_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_larger_tailBound_tailBound_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (C.with_larger_tailBound hle).tailBound = tailBound' := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_larger_tailBound_tailBound C hle

/--
[with_tailEnvelope_and_tailBound_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBound_support_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (henvelope_nonneg : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → C.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg hweight_le henvelope_sum).support = C.support := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_tailEnvelope_and_tailBound_support C envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBound_finitePrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBound_finitePrefix_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (henvelope_nonneg : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → C.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg hweight_le henvelope_sum).finitePrefix = C.finitePrefix := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_tailEnvelope_and_tailBound_finitePrefix C envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBound_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBound_weight_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (henvelope_nonneg : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → C.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg hweight_le henvelope_sum).weight = C.weight := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_tailEnvelope_and_tailBound_weight C envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBound_envelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBound_envelope_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (henvelope_nonneg : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → C.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg hweight_le henvelope_sum).envelope = envelope' := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_tailEnvelope_and_tailBound_envelope C envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBound_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBound_tailBound_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (henvelope_nonneg : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ C.support → a ∉ C.finitePrefix → C.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ C.support \ C.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (C.with_tailEnvelope_and_tailBound envelope' henvelope_nonneg hweight_le henvelope_sum).tailBound = tailBound' := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.with_tailEnvelope_and_tailBound_tailBound C envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[tsum_le_prefix_sum_add_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tsum_le_prefix_sum_add_tailBound_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α} :
-- imply
  (∑' a, C.weight a) ≤ (∑ a ∈ C.finitePrefix, C.weight a) + C.tailBound := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tsum_le_prefix_sum_add_tailBound C

/--
[tsum_le_prefix_sum_add_of_tailBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tsum_le_prefix_sum_add_of_tailBound_le_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
  {tailBound' : ℝ}
-- given
  (hle : C.tailBound ≤ tailBound') :
-- imply
  (∑' a, C.weight a) ≤ (∑ a ∈ C.finitePrefix, C.weight a) + tailBound' := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tsum_le_prefix_sum_add_of_tailBound_le C hle

/--
[summable_total_of_zero_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma summable_total_of_zero_off_support_eq
  {S : ContributionSplit α}
  {support : Finset α}
-- given
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0) :
-- imply
  Summable S.totalContribution := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.summable_total_of_zero_off_support S support hzero

/--
[tsum_total_eq_sum_of_zero_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tsum_total_eq_sum_of_zero_off_support_eq
  {S : ContributionSplit α}
  {support : Finset α}
-- given
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0) :
-- imply
  (∑' a, S.totalContribution a) = ∑ a ∈ support, S.totalContribution a := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.tsum_total_eq_sum_of_zero_off_support S support hzero

/--
[total_le_finiteBound_add_tailEnvelopeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma total_le_finiteBound_add_tailEnvelopeOn_eq
  [DecidableEq Case]
  {S : ContributionSplit α}
  {support : Finset α}
  {T : RatInterval.CaseTable Case}
  {classify : α → Case}
  {finiteBound : ℝ}
  {tailEnvelope : α → ℝ}
  {a : α}
-- given
  (hadd : S.Additive)
  (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
  (htail : S.TailEnvelopeOn support tailEnvelope)
  (ha : a ∈ support) :
-- imply
  S.totalContribution a ≤ finiteBound + tailEnvelope a := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.total_le_finiteBound_add_tailEnvelopeOn S support tailEnvelope hadd hfinite htail ha

/--
[tsum_total_le_prefix_sum_add_tableTailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tsum_total_le_prefix_sum_add_tableTailBound_eq
  [DecidableEq α]
  [DecidableEq Case]
  {S : ContributionSplit α}
  {support finitePrefix : Finset α}
  {T : RatInterval.CaseTable Case}
  {classify : α → Case}
  {finiteBound tailEnvelopeBound : ℝ}
  {tailEnvelope : α → ℝ}
-- given
  (hprefix : finitePrefix ⊆ support)
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
  (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
  (hadd : S.Additive)
  (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
  (htail : S.TailEnvelopeOn support tailEnvelope)
  (htailSum : (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (∑ a ∈ finitePrefix, S.totalContribution a) + (((support \ finitePrefix).card : ℝ) * finiteBound + tailEnvelopeBound) := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.tsum_total_le_prefix_sum_add_tableTailBound S support finitePrefix tailEnvelope hprefix hzero hnonneg hadd hfinite htail htailSum

/--
[tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean)
-/
@[path]
private lemma tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn_eq
  [DecidableEq Case]
  {S : ContributionSplit α}
  {support : Finset α}
  {T : RatInterval.CaseTable Case}
  {classify : α → Case}
  {finiteBound tailBound : ℝ}
  {tailEnvelope : α → ℝ}
-- given
  (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
  (hadd : S.Additive)
  (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
  (htail : S.TailEnvelopeOn support tailEnvelope)
  (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑' a, S.totalContribution a) ≤ (support.card : ℝ) * finiteBound + tailBound := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn S support tailEnvelope hzero hadd hfinite htail htailSum


-- created on 2026-10-23
