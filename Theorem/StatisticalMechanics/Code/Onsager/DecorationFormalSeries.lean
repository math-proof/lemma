/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalSeries


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_finsuppTotalDegree_add
    {E : Type*} [DecidableEq E] (m n : E →₀ ℕ) :
    ons_finsuppTotalDegree (m + n) =
      ons_finsuppTotalDegree m + ons_finsuppTotalDegree n := by
  unfold ons_finsuppTotalDegree
  rw [Finsupp.sum_add_index]
  · simp
  · simp

@[simp] theorem ons_finsuppTotalDegree_single
    {E : Type*} [DecidableEq E] (edge : E) (n : ℕ) :
    ons_finsuppTotalDegree (Finsupp.single edge n) = n := by
  unfold ons_finsuppTotalDegree
  rw [Finsupp.sum_single_index]
  simp

theorem ons_finsuppTotalDegree_finset_sum
    {I E : Type*} [Fintype I] [DecidableEq E] (m : I → E →₀ ℕ) :
    ons_finsuppTotalDegree (∑ i, m i) =
      ∑ i, ons_finsuppTotalDegree (m i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [ons_finsuppTotalDegree]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ons_finsuppTotalDegree_add, ih]

theorem ons_decTransitionExponent_totalDegree_pos
    (L : ℕ) (d₂ d₁ : ons_Dart L) :
    0 < ons_finsuppTotalDegree
      (ons_decTransitionExponent L d₂ d₁) := by
  unfold ons_decTransitionExponent
  rw [ons_finsuppTotalDegree_add,
    ons_finsuppTotalDegree_single]
  omega

theorem ons_decLoopExponent_length_le
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    n ≤ ons_finsuppTotalDegree (ons_decLoopExponent L d) := by
  unfold ons_decLoopExponent
  rw [ons_finsuppTotalDegree_finset_sum]
  calc
    n = ∑ _k : Fin n, 1 := by simp
    _ ≤ ∑ k : Fin n,
        ons_finsuppTotalDegree
          (ons_decTransitionExponent L (d k) (d (k + 1))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact ons_decTransitionExponent_totalDegree_pos L _ _


end StatMech.Onsager
