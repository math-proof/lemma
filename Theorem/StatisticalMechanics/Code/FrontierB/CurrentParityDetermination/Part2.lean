/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
import Def.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part2
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

theorem boolAvoid_mass_eq_apply_add_lower {I : Type*}
    [Fintype I] [DecidableEq I] (p : PMF (I → Bool)) (b : I → Bool) :
    p.toMeasure (boolAvoid (Finset.univ \ boolSupport b)) =
      p b + ∑ a ∈ boolLower b, p a := by
  rw [PMF.toMeasure_apply_fintype]
  rw [show (∑ x, (boolAvoid (Finset.univ \ boolSupport b)).indicator p x) =
      ∑ x ∈ Finset.univ.filter
        (fun a => boolSupport a ⊆ boolSupport b), p x by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hsub : boolSupport a ⊆ boolSupport b <;>
      simp [Set.indicator, mem_boolAvoid_compl_support_iff, hsub]
    ]
  rw [show Finset.univ.filter
      (fun a => boolSupport a ⊆ boolSupport b) = insert b (boolLower b) by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, boolLower]
    constructor
    · intro hsub
      by_cases heq : boolSupport a = boolSupport b
      · exact Or.inl (boolSupport_injective heq)
      · exact Or.inr (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩)
    · rintro (rfl | hproper)
      · exact Finset.Subset.rfl
      · exact hproper.subset]
  have hb : b ∉ boolLower b := by
    simp only [boolLower, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    exact h.2 Finset.Subset.rfl
  rw [Finset.sum_insert hb]

theorem PMF.ext_of_boolAvoid_eq {I : Type*}
    [Fintype I] [DecidableEq I] {p q : PMF (I → Bool)}
    (h : ∀ T : Finset I, p.toMeasure (boolAvoid T) =
      q.toMeasure (boolAvoid T)) :
    p = q := by
  apply PMF.ext
  intro b
  induction n : (boolSupport b).card using Nat.strong_induction_on generalizing b with
  | h n ih =>
      have hmass := h (Finset.univ \ boolSupport b)
      rw [boolAvoid_mass_eq_apply_add_lower,
        boolAvoid_mass_eq_apply_add_lower] at hmass
      have hlower : (∑ a ∈ boolLower b, p a) =
          ∑ a ∈ boolLower b, q a := by
        apply Finset.sum_congr rfl
        intro a ha
        have hproper : boolSupport a ⊂ boolSupport b :=
          (Finset.mem_filter.mp ha).2
        apply ih (boolSupport a).card
          (by simpa [← n] using Finset.card_lt_card hproper) a rfl
      rw [hlower] at hmass
      apply (ENNReal.add_right_inj (ENNReal.sum_ne_top.mpr
        (fun a ha => PMF.apply_ne_top q a))).mp
      simpa [add_comm] using hmass

end StatMech.FrontierB
