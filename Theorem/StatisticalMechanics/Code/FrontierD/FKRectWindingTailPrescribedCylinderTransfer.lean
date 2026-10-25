/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectIndexedPatternPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer
open Finset
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech

noncomputable section

@[simp] theorem fkRectForceLocalPattern_of_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (eta : FKRectLocalPattern R I) (omega : R.Configuration)
    {a : R.EdgeIndex} (ha : a ∈ I) :
    fkRectForceLocalPattern R I eta omega a = eta ⟨a, ha⟩ := by
  simp [fkRectForceLocalPattern, fkRectLocalPatternExtension, ha]

@[simp] theorem fkRectForceLocalPattern_of_not_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (eta : FKRectLocalPattern R I) (omega : R.Configuration)
    {a : R.EdgeIndex} (ha : a ∉ I) :
    fkRectForceLocalPattern R I eta omega a = omega a := by
  simp [fkRectForceLocalPattern, ha]


theorem fkRectCritical_cFE_pow_mul_forceLocalPattern_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (eta : FKRectLocalPattern R I)
    (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q
          (fkRectForceLocalPattern R I eta ⁻¹' A) ≤
      fkRectCriticalEventMass R q A := by
  exact
    fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event
      R hq I (fkRectLocalPatternExtension R I eta) A


theorem fkRectCritical_cFE_pow_mul_event_le_two_pow_mul_of_localRepair
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (Source Target : Set R.Configuration)
    (hrepair : ∀ omega, omega ∈ Source →
      ∃ eta : FKRectLocalPattern R I,
        fkRectForceLocalPattern R I eta omega ∈ Target) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q Source ≤
      (2 ^ I.card : Nat) * fkRectCriticalEventMass R q Target := by
  classical
  let Pattern := FKRectLocalPattern R I
  let A : Pattern → Set R.Configuration := fun eta =>
    fkRectForceLocalPattern R I eta ⁻¹' Target
  have hsubset : Source ⊆
      fkRectFiniteEventUnion (Finset.univ : Finset Pattern) A := by
    intro omega homega
    obtain ⟨eta, heta⟩ := hrepair omega homega
    exact ⟨eta, Finset.mem_univ eta, heta⟩
  have hmono := fkRectCriticalEventMass_mono R
    (lt_of_lt_of_le zero_lt_one hq) hsubset
  have hunion := fkRectCriticalEventMass_finiteUnion_le_sum R
    (lt_of_lt_of_le zero_lt_one hq)
    (Finset.univ : Finset Pattern) A
  have hc : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    fkRectCritical_cFE_nonneg hq
  calc
    FK.cFE (fkRectCriticalP q) q ^ I.card *
          fkRectCriticalEventMass R q Source ≤
        FK.cFE (fkRectCriticalP q) q ^ I.card *
          fkRectCriticalEventMass R q
            (fkRectFiniteEventUnion (Finset.univ : Finset Pattern) A) :=
      mul_le_mul_of_nonneg_left hmono (pow_nonneg hc _)
    _ ≤ FK.cFE (fkRectCriticalP q) q ^ I.card *
        ∑ eta : Pattern, fkRectCriticalEventMass R q (A eta) :=
      mul_le_mul_of_nonneg_left hunion (pow_nonneg hc _)
    _ = ∑ eta : Pattern,
        FK.cFE (fkRectCriticalP q) q ^ I.card *
          fkRectCriticalEventMass R q (A eta) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _eta : Pattern, fkRectCriticalEventMass R q Target := by
      apply Finset.sum_le_sum
      intro eta heta
      exact
        fkRectCritical_cFE_pow_mul_forceLocalPattern_preimage_le_event
          R hq I eta Target
    _ = (2 ^ I.card : Nat) * fkRectCriticalEventMass R q Target := by
      simp [Pattern, FKRectLocalPattern]


theorem fkRectCriticalWindingTailMass_eq_eventMass
    (R : FKRectTorus) (q : Real) (r : Nat) :
    fkRectCriticalWindingTailMass R q r =
      fkRectCriticalEventMass R q
        {omega | r ≤ fkRectUnorientedVerticalWindingNumber R omega} := by
  unfold fkRectCriticalWindingTailMass fkRectCriticalEventMass
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases htail : r ≤ fkRectUnorientedVerticalWindingNumber R omega <;>
    simp [Set.indicator, htail]


end
end StatMech.FrontierD
