/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Structure.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


noncomputable def ofFiniteWitnessPackage
    (W : FiniteWitnessPackage (α := α) M) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate := W.tailCertificate.toInfiniteTailCertificate


noncomputable def ofTailEnvelope
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_tailEnvelope : Summable tailEnvelope)
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    TailSummability.InfiniteTailCertificate.of_tailEnvelope
      finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg
      hweight_le_tailEnvelope hsummable_tailEnvelope htailEnvelope_tsum_le


noncomputable def ofMaskedTailEnvelope
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (finitePrefix : Finset α) (weight tailEnvelope : α → ℝ)
    {tailBound : ℝ}
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (henvelope_nonneg_off :
      ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (hweight_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → weight a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope
      finitePrefix weight tailEnvelope hweight_nonneg henvelope_nonneg_off
      hweight_le_tailEnvelope hsummable_masked hmasked_tsum_le


noncomputable def ofContributionSplitInfiniteTail
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (totalEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (henvelope_nonneg : ∀ a, 0 ≤ totalEnvelope a)
    (htotal_le_totalEnvelope :
      ∀ a, a ∉ finitePrefix → S.totalContribution a ≤ totalEnvelope a)
    (hsummable_totalEnvelope : Summable totalEnvelope)
    (htotalEnvelope_tsum_le : (∑' a, totalEnvelope a) ≤ tailBound) :
    InfiniteTailWitnessPackage (α := α) M :=
  ofTailEnvelope M scale hthermal stable finitePrefix S.totalContribution
    totalEnvelope htotal_nonneg henvelope_nonneg htotal_le_totalEnvelope
    hsummable_totalEnvelope htotalEnvelope_tsum_le


noncomputable def ofContributionSplitTailEnvelope
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (tailEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_tailEnvelope : Summable tailEnvelope)
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    S.infiniteTailCertificate_of_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le


noncomputable def ofContributionSplitMaskedTailEnvelope
    (M : CriticalModel ι) {nStable : ℕ}
    (scale : BlockScale) {thermal : ℝ} (hthermal : 1 < thermal)
    (stable : FiniteStableWitness nStable)
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (tailEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg_off :
      ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    InfiniteTailWitnessPackage (α := α) M where
  nStable := nStable
  scale := scale
  thermal := thermal
  thermal_gt_one := hthermal
  stable := stable
  tailCertificate :=
    S.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le


end InfiniteTailWitnessPackage
end Exact3D
end StatMech
