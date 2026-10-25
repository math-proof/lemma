/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Foundations.Kingman
open MeasureTheory Filter Topology


namespace StatMech

namespace Kingman

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


namespace SubadditiveCocycle

variable {T : α → α} {X : ℕ → α → ℝ}


theorem expSeq_subadditive (h : SubadditiveCocycle T μ X) (m n : ℕ) :
    expSeq X μ (m + n) ≤ expSeq X μ m + expSeq X μ n := by
  have hint : ∫ x, X (m + n) x ∂μ ≤ ∫ x, (X m x + X n (T^[m] x)) ∂μ := by
    refine integral_mono_ae (h.integrable (m + n)) ?_ (h.subadditive m n)
    exact (h.integrable m).add
      ((h.measurePreserving.iterate m).integrable_comp_of_integrable (h.integrable n))
  calc expSeq X μ (m + n) = ∫ x, X (m + n) x ∂μ := rfl
    _ ≤ ∫ x, (X m x + X n (T^[m] x)) ∂μ := hint
    _ = (∫ x, X m x ∂μ) + ∫ x, X n (T^[m] x) ∂μ := by
        rw [integral_add (h.integrable m)]
        exact (h.measurePreserving.iterate m).integrable_comp_of_integrable (h.integrable n)
    _ = expSeq X μ m + expSeq X μ n := by
        rw [integral_comp_iterate T h.measurePreserving (X n)
          (h.integrable n).aestronglyMeasurable]
        rfl


theorem subadditive_expSeq (h : SubadditiveCocycle T μ X) :
    Subadditive (expSeq X μ) := h.expSeq_subadditive


theorem ae_le_birkhoffSum (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, ∀ n, 1 ≤ n → X n x ≤ birkhoffSum T (X 1) n x := by
  have hstep : ∀ᵐ x ∂μ, ∀ n, X (n + 1) x ≤ X n x + X 1 (T^[n] x) := by
    rw [ae_all_iff]
    intro n
    exact h.subadditive n 1
  filter_upwards [hstep] with x hx
  intro n hn
  induction n with
  | zero => exact absurd hn (by norm_num)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [birkhoffSum_one]
    · calc X (k + 1) x ≤ X k x + X 1 (T^[k] x) := hx k
        _ ≤ birkhoffSum T (X 1) k x + X 1 (T^[k] x) := by gcongr; exact ih hk
        _ = birkhoffSum T (X 1) (k + 1) x := (birkhoffSum_succ_apply T (X 1) k x).symm


theorem integrable_birkhoffSum (h : SubadditiveCocycle T μ X) (n : ℕ) :
    Integrable (fun x => birkhoffSum T (X 1) n x) μ := by
  simp only [birkhoffSum]
  refine integrable_finsetSum _ ?_
  intro i _
  exact (h.measurePreserving.iterate i).integrable_comp_of_integrable (h.integrable 1)


theorem expSeq_le_nsmul (h : SubadditiveCocycle T μ X) {n : ℕ} (hn : 1 ≤ n) :
    expSeq X μ n ≤ n • expSeq X μ 1 := by
  calc expSeq X μ n = ∫ x, X n x ∂μ := rfl
    _ ≤ ∫ x, birkhoffSum T (X 1) n x ∂μ := by
        refine integral_mono_ae (h.integrable n) (h.integrable_birkhoffSum n) ?_
        filter_upwards [h.ae_le_birkhoffSum] with x hx using hx n hn
    _ = ∑ i ∈ Finset.range n, ∫ x, X 1 (T^[i] x) ∂μ := by
        simp only [birkhoffSum]
        rw [integral_finsetSum]
        intro i _
        exact (h.measurePreserving.iterate i).integrable_comp_of_integrable (h.integrable 1)
    _ = ∑ _i ∈ Finset.range n, expSeq X μ 1 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_comp_iterate T h.measurePreserving (X 1)
          (h.integrable 1).aestronglyMeasurable]
        rfl
    _ = n • expSeq X μ 1 := by rw [Finset.sum_const, Finset.card_range]


end SubadditiveCocycle
end Kingman
end StatMech
