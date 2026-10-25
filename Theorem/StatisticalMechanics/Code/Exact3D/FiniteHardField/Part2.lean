/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part2
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

theorem tendsto_exp_neg_atTop :
    Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot


theorem hardFieldFactor_tendsto {α : Type*} (good : α → Prop)
    [DecidablePred good] (a : α) :
    Tendsto (fun H : ℝ => hardFieldFactor good H a) atTop
      (𝓝 (if good a then 1 else 0)) := by
  by_cases ha : good a
  · simp [hardFieldFactor, ha]
  · simpa [hardFieldFactor, ha] using tendsto_exp_neg_atTop


theorem hardFieldNumeratorSummand_tendsto {α : Type*}
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) (a : α) :
    Tendsto
      (fun H : ℝ => base a * hardFieldFactor good H a * obs a)
      atTop
      (𝓝 (if good a then base a * obs a else 0)) := by
  by_cases ha : good a
  · simp [hardFieldFactor, ha]
  · have hfactor :
        Tendsto (fun H : ℝ => hardFieldFactor good H a) atTop (𝓝 0) := by
      simpa [hardFieldFactor, ha] using tendsto_exp_neg_atTop
    have hmul :
        Tendsto
          (fun H : ℝ => (base a * obs a) * hardFieldFactor good H a)
          atTop
          (𝓝 ((base a * obs a) * 0)) :=
      Filter.Tendsto.const_mul (base a * obs a) hfactor
    have hrewrite :
        (fun H : ℝ => base a * hardFieldFactor good H a * obs a)
          =
        (fun H : ℝ => (base a * obs a) * hardFieldFactor good H a) := by
      funext H
      ring
    simpa [ha, hrewrite] using hmul


theorem hardFieldDenominatorSummand_tendsto {α : Type*}
    (good : α → Prop) [DecidablePred good] (base : α → ℝ) (a : α) :
    Tendsto
      (fun H : ℝ => base a * hardFieldFactor good H a)
      atTop
      (𝓝 (if good a then base a else 0)) := by
  by_cases ha : good a
  · simp [hardFieldFactor, ha]
  · have hfactor :
        Tendsto (fun H : ℝ => hardFieldFactor good H a) atTop (𝓝 0) := by
      simpa [hardFieldFactor, ha] using tendsto_exp_neg_atTop
    have hmul :
        Tendsto
          (fun H : ℝ => base a * hardFieldFactor good H a)
          atTop
          (𝓝 (base a * 0)) :=
      Filter.Tendsto.const_mul (base a) hfactor
    simpa [ha] using hmul


theorem hardFieldNumerator_tendsto {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) :
    Tendsto (fun H : ℝ => hardFieldNumerator s good base obs H)
      atTop
      (𝓝 (hardFieldLimitNumerator s good base obs)) := by
  unfold hardFieldNumerator hardFieldLimitNumerator
  exact tendsto_finsetSum s (fun a _ =>
    hardFieldNumeratorSummand_tendsto good base obs a)


theorem hardFieldDenominator_tendsto {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base : α → ℝ) :
    Tendsto (fun H : ℝ => hardFieldDenominator s good base H)
      atTop
      (𝓝 (hardFieldLimitDenominator s good base)) := by
  unfold hardFieldDenominator hardFieldLimitDenominator
  exact tendsto_finsetSum s (fun a _ =>
    hardFieldDenominatorSummand_tendsto good base a)


theorem hardFieldRatio_tendsto {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ)
    (hden : hardFieldLimitDenominator s good base ≠ 0) :
    Tendsto (fun H : ℝ => hardFieldRatio s good base obs H)
      atTop
      (𝓝 (hardFieldLimitRatio s good base obs)) := by
  unfold hardFieldRatio hardFieldLimitRatio
  exact Filter.Tendsto.div
    (hardFieldNumerator_tendsto s good base obs)
    (hardFieldDenominator_tendsto s good base)
    hden


theorem hardFieldLimitNumerator_eq_filter {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) :
    hardFieldLimitNumerator s good base obs =
      ∑ a ∈ s.filter good, base a * obs a := by
  classical
  unfold hardFieldLimitNumerator
  rw [← Finset.sum_filter]


theorem hardFieldLimitDenominator_eq_filter {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base : α → ℝ) :
    hardFieldLimitDenominator s good base =
      ∑ a ∈ s.filter good, base a := by
  classical
  unfold hardFieldLimitDenominator
  rw [← Finset.sum_filter]


theorem hardFieldLimitDenominator_pos_of_exists_pos {α : Type*}
    (s : Finset α) (good : α → Prop) [DecidablePred good] (base : α → ℝ)
    (hnonneg : ∀ a, a ∈ s → good a → 0 ≤ base a)
    (hpos : ∃ a, a ∈ s ∧ good a ∧ 0 < base a) :
    0 < hardFieldLimitDenominator s good base := by
  classical
  rw [hardFieldLimitDenominator_eq_filter]
  refine Finset.sum_pos' ?_ ?_
  · intro a ha
    exact hnonneg a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
  · obtain ⟨a, has, hgood, hbase⟩ := hpos
    exact ⟨a, Finset.mem_filter.mpr ⟨has, hgood⟩, hbase⟩


theorem hardFieldLimitDenominator_ne_zero_of_exists_pos {α : Type*}
    (s : Finset α) (good : α → Prop) [DecidablePred good] (base : α → ℝ)
    (hnonneg : ∀ a, a ∈ s → good a → 0 ≤ base a)
    (hpos : ∃ a, a ∈ s ∧ good a ∧ 0 < base a) :
    hardFieldLimitDenominator s good base ≠ 0 :=
  (hardFieldLimitDenominator_pos_of_exists_pos s good base hnonneg hpos).ne'


end Exact3D
end StatMech
