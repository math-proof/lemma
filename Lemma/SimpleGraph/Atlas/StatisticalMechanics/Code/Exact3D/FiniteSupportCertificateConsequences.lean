import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
open StatMech StatMech.Exact3D StatMech.Exact3D.TailSummability StatMech.Exact3D.TailSummability.FiniteSupportCertificate


/--
[finitePrefix_eq_support_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteSupportCertificateConsequences.lean)
-/
@[path]
private lemma finitePrefix_eq_support_of_support_subset_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
-- given
  (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
-- imply
  C.finitePrefix = C.support := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.finitePrefix_eq_support_of_support_subset C hsupport_subset_prefix

/--
[tailSupport_eq_empty_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteSupportCertificateConsequences.lean)
-/
@[path]
private lemma tailSupport_eq_empty_of_support_subset_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
-- given
  (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
-- imply
  C.tailSupport = ∅ := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tailSupport_eq_empty_of_support_subset C hsupport_subset_prefix

/--
[support_sum_eq_finitePrefix_sum_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteSupportCertificateConsequences.lean)
-/
@[path]
private lemma support_sum_eq_finitePrefix_sum_of_support_subset_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
-- given
  (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
-- imply
  (∑ a ∈ C.support, C.weight a) = ∑ a ∈ C.finitePrefix, C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.support_sum_eq_finitePrefix_sum_of_support_subset C hsupport_subset_prefix

/--
[tsum_eq_finitePrefix_sum_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteSupportCertificateConsequences.lean)
-/
@[path]
private lemma tsum_eq_finitePrefix_sum_of_support_subset_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
-- given
  (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
-- imply
  (∑' a, C.weight a) = ∑ a ∈ C.finitePrefix, C.weight a := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tsum_eq_finitePrefix_sum_of_support_subset C hsupport_subset_prefix

/--
[tail_sum_eq_zero_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteSupportCertificateConsequences.lean)
-/
@[path]
private lemma tail_sum_eq_zero_of_support_subset_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
-- given
  (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
-- imply
  (∑ a ∈ C.tailSupport, C.weight a) = 0 := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.tail_sum_eq_zero_of_support_subset C hsupport_subset_prefix

/--
[envelope_tail_sum_eq_zero_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteSupportCertificateConsequences.lean)
-/
@[path]
private lemma envelope_tail_sum_eq_zero_of_support_subset_eq
  [DecidableEq α]
  {C : FiniteSupportCertificate α}
-- given
  (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
-- imply
  (∑ a ∈ C.tailSupport, C.envelope a) = 0 := by
-- proof
  apply StatMech.Exact3D.TailSummability.FiniteSupportCertificate.envelope_tail_sum_eq_zero_of_support_subset C hsupport_subset_prefix


-- created on 2026-10-23
