/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanSigned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.Kingman.Part3
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part4
import Theorem.StatisticalMechanics.Code.Foundations.KingmanAE.Part4
import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling.Part2
import Def.StatisticalMechanics.Code.Foundations.KingmanSigned
open MeasureTheory Filter Topology ENNReal


namespace StatMech

namespace KingmanSigned

open Kingman BirkhoffAE KingmanAE KingmanFilling

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}


omit [MeasurableSpace α] in

theorem addCoc_add (m n : ℕ) (x : α) :
    addCoc T X (m + n) x = addCoc T X m x + addCoc T X n (T^[m] x) :=
  birkhoffSum_add T (X 1) m n x

omit [MeasurableSpace α] in

theorem Wc_eq_neg (n : ℕ) (x : α) : Wc T X n x = - Zc T X n x := by
  unfold Wc Zc; rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  · simp only [if_neg hn]; ring

omit [MeasurableSpace α] in

theorem Zc_one (x : α) : Zc T X 1 x = 0 := by
  unfold Zc addCoc; simp [birkhoffSum_one]

omit [MeasurableSpace α] in

theorem Zc_div_eq {n : ℕ} (hn : 1 ≤ n) (x : α) :
    Zc T X n x / n = (addCoc T X n x - X n x) / n := by
  unfold Zc; rw [if_neg (by omega)]


theorem integrable_addCoc (h : SubadditiveCocycle T μ X) (n : ℕ) :
    Integrable (addCoc T X n) μ := by
  unfold addCoc; simp only [birkhoffSum]
  exact integrable_finsetSum _
    (fun i _ => (h.measurePreserving.iterate i).integrable_comp_of_integrable (h.integrable 1))


theorem integrable_Wc (h : SubadditiveCocycle T μ X) (n : ℕ) :
    Integrable (Wc T X n) μ := by
  unfold Wc
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  · simp only [if_neg hn]
    exact (h.integrable n).sub (integrable_addCoc h n)


theorem integrable_Zc (h : SubadditiveCocycle T μ X) (n : ℕ) :
    Integrable (Zc T X n) μ := by
  have := integrable_Wc h n
  rw [show Zc T X n = fun x => - Wc T X n x by funext x; rw [Wc_eq_neg]; ring]
  exact this.neg


theorem Wc_subaddCocycle (h : SubadditiveCocycle T μ X) : SubadditiveCocycle T μ (Wc T X) := by
  refine ⟨h.measurePreserving, integrable_Wc h, ?_⟩
  intro m n
  filter_upwards [h.subadditive m n] with x hx
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    rcases eq_or_ne n 0 with hn | hn
    · subst hn; simp [Wc]
    · have h0 : Wc T X 0 x = 0 := by simp [Wc]
      simp only [h0, zero_add, Function.iterate_zero, id, le_refl]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have h0 : Wc T X 0 (T^[m] x) = 0 := by simp [Wc]
    simp only [h0, add_zero, le_refl]
  have hmn : m + n ≠ 0 := by omega
  simp only [Wc, if_neg hm, if_neg hn, if_neg hmn, addCoc_add]
  linarith [hx]


theorem Wc_nonpos_ae (h : SubadditiveCocycle T μ X) {n : ℕ} (hn : 1 ≤ n) : Wc T X n ≤ᵐ[μ] 0 := by
  filter_upwards [h.ae_le_birkhoffSum] with x hx
  simp only [Wc, if_neg (by omega : n ≠ 0), addCoc, Pi.zero_apply]
  linarith [hx n hn]


theorem Zc_nonneg_ae (h : SubadditiveCocycle T μ X) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ᵐ[μ] Zc T X n := by
  filter_upwards [Wc_nonpos_ae h hn] with x hx
  rw [Wc_eq_neg] at hx; simp only [Pi.zero_apply] at hx ⊢; linarith


theorem Zc_nonneg_ae_all (h : SubadditiveCocycle T μ X) (n : ℕ) : 0 ≤ᵐ[μ] Zc T X n := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; filter_upwards with x; simp [Zc]
  · exact Zc_nonneg_ae h (by omega)


end KingmanSigned
end StatMech
