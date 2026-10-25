/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.MaximalErgodicGarsia
import Def.StatisticalMechanics.Code.Foundations.BirkhoffPointwise
open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


omit [MeasurableSpace α] in
theorem IsInvariantSet.iterate {E : Set α} (hE : IsInvariantSet T E) (k : ℕ) (x : α) :
    x ∈ E ↔ T^[k] x ∈ E := by
  induction k with
  | zero => simp
  | succ k ih => rw [ih, Function.iterate_succ_apply', hE]

omit [MeasurableSpace α] in


theorem birkhoffSum_indicator {E : Set α} (hE : IsInvariantSet T E) (g : α → ℝ) (n : ℕ) (x : α) :
    birkhoffSum T (E.indicator g) n x = E.indicator (fun y => birkhoffSum T g n y) x := by
  simp only [birkhoffSum, Set.indicator]
  by_cases hx : x ∈ E
  · simp only [hx, if_true]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [if_pos ((hE.iterate k x).mp hx)]
  · simp only [hx, if_false]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [if_neg (fun h => hx ((hE.iterate k x).mpr h))]

open StatMech.GarsiaMax in
omit [MeasurableSpace α] in


theorem maxPartialSum_indicator {E : Set α} (hE : IsInvariantSet T E) (g : α → ℝ) {N : ℕ}
    (hN : 1 ≤ N) (x : α) :
    maxPartialSum T (E.indicator g) N hN x =
      E.indicator (fun y => maxPartialSum T g N hN y) x := by
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx]
    unfold maxPartialSum
    refine Finset.sup'_congr _ rfl (fun n _ => ?_)
    rw [birkhoffSum_indicator hE g n x, Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx]
    unfold maxPartialSum
    have h0 : ∀ n ∈ Finset.Icc 1 N, birkhoffSum T (E.indicator g) n x = 0 := by
      intro n _
      rw [birkhoffSum_indicator hE g n x, Set.indicator_of_notMem hx]
    rw [Finset.sup'_congr _ rfl h0]
    simp

open StatMech.GarsiaMax in
omit [MeasurableSpace α] in

theorem setOf_maxPartialSum_indicator {E : Set α} (hE : IsInvariantSet T E) (g : α → ℝ) {N : ℕ}
    (hN : 1 ≤ N) :
    {x | 0 < maxPartialSum T (E.indicator g) N hN x}
      = E ∩ {x | 0 < maxPartialSum T g N hN x} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, maxPartialSum_indicator hE g hN x]
  by_cases hx : x ∈ E
  · simp [hx]
  · simp [hx]

open StatMech.GarsiaMax in
omit [MeasurableSpace α] in

theorem maxPartialSum_mono (g : α → ℝ) {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : N ≤ M) (x : α) :
    maxPartialSum T g N hN x ≤ maxPartialSum T g M hM x := by
  obtain ⟨n, hn1, hn2, hneq⟩ := exists_eq_maxPartialSum hN x
  rw [← hneq]
  exact birkhoffSum_le_maxPartialSum hM hn1 (le_trans hn2 hNM) x


omit [MeasurableSpace α] in

theorem cocycle_avg (x : α) (n : ℕ) :
    ((n : ℝ) + 1) * birkhoffAverage ℝ T f (n + 1) x
      = f x + (n : ℝ) * birkhoffAverage ℝ T f n (T x) := by
  simp only [birkhoffAverage, smul_eq_mul]
  rw [birkhoffSum_succ_apply' T f n x]
  have e1 : ((n : ℝ) + 1) * ((↑(n + 1))⁻¹ * (f x + birkhoffSum T f n (T x)))
      = f x + birkhoffSum T f n (T x) := by
    rw [show ((n : ℕ) + 1 : ℕ) = (n + 1) from rfl]; push_cast; field_simp
  rw [e1]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [birkhoffSum_zero]
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp

omit [MeasurableSpace α] in

theorem avg_comp_eq (x : α) {n : ℕ} (hn : 1 ≤ n) :
    birkhoffAverage ℝ T f n (T x)
      = (((n : ℝ) + 1) / n) * birkhoffAverage ℝ T f (n + 1) x - (f x) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have := cocycle_avg (T := T) (f := f) x n
  field_simp at this ⊢; linarith [this]

omit [MeasurableSpace α] in

theorem avg_succ_eq (x : α) (n : ℕ) :
    birkhoffAverage ℝ T f (n + 1) x
      = ((n : ℝ) / (n + 1)) * birkhoffAverage ℝ T f n (T x) + (f x) / (n + 1) := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have := cocycle_avg (T := T) (f := f) x n
  field_simp at this ⊢; linarith [this]

omit [MeasurableSpace α] in

theorem limsup_avg_comp_le (x : α) :
    limsup (fun n => ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop
      ≤ limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop := by
  set L : EReal := limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop with hL
  rw [limsup_le_iff']
  intro y hyL
  obtain ⟨z, hLz, hzy⟩ := EReal.lt_iff_exists_real_btwn.mp hyL
  have h0 : ∀ᶠ n in atTop, ((birkhoffAverage ℝ T f n x : ℝ) : EReal) < (z : EReal) :=
    eventually_lt_of_limsup_lt (hL ▸ hLz)
  have hev : ∀ᶠ n in atTop, birkhoffAverage ℝ T f (n + 1) x < z := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually h0] with n hn
    exact_mod_cast hn
  have hr : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / n) * z - (f x) / n) atTop (𝓝 z) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
      have key : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) / n = 1 + 1 / (n : ℝ) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : (n : ℝ) ≠ 0 := by positivity
        field_simp
      rw [tendsto_congr' key]
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => (f x) / (n : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := f x)).div_atTop tendsto_natCast_atTop_atTop
    simpa using (h1.mul tendsto_const_nhds).sub h2
  have hbound : ∀ᶠ n in atTop,
      birkhoffAverage ℝ T f n (T x) < (((n : ℝ) + 1) / n) * z - (f x) / n := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    rw [avg_comp_eq x hn1]
    have hpos : 0 < ((n : ℝ) + 1) / n := by
      have : (0 : ℝ) < n := by exact_mod_cast hn1
      positivity
    have hmul : (((n : ℝ) + 1) / n) * birkhoffAverage ℝ T f (n + 1) x < (((n : ℝ) + 1) / n) * z :=
      mul_lt_mul_of_pos_left hn hpos
    linarith
  rcases eq_top_or_lt_top y with hytop | hytop
  · filter_upwards with n; rw [hytop]; exact le_top
  · have hybot : y ≠ ⊥ := fun h => by rw [h] at hzy; exact not_lt_bot hzy
    have hyr : y = (y.toReal : EReal) := (EReal.coe_toReal hytop.ne hybot).symm
    have hzyr : z < y.toReal := by rw [hyr] at hzy; exact_mod_cast hzy
    have hrlt : ∀ᶠ n : ℕ in atTop, (((n : ℝ) + 1) / n) * z - (f x) / n < y.toReal :=
      hr.eventually (eventually_lt_nhds hzyr)
    filter_upwards [hbound, hrlt] with n hn1 hn2
    have hlt : birkhoffAverage ℝ T f n (T x) < y.toReal := lt_trans hn1 hn2
    rw [hyr]; exact_mod_cast hlt.le

omit [MeasurableSpace α] in

theorem limsup_avg_le_comp (x : α) :
    limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop
      ≤ limsup (fun n => ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop := by
  set L : EReal := limsup (fun n => ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop with hL
  rw [limsup_le_iff']
  intro y hyL
  obtain ⟨z, hLz, hzy⟩ := EReal.lt_iff_exists_real_btwn.mp hyL
  have h0 : ∀ᶠ n in atTop, ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal) < (z : EReal) :=
    eventually_lt_of_limsup_lt (hL ▸ hLz)
  have hev : ∀ᶠ n in atTop, birkhoffAverage ℝ T f n (T x) < z := by
    filter_upwards [h0] with n hn; exact_mod_cast hn
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) / (n + 1)) * z + (f x) / (n + 1)) atTop (𝓝 z) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
      have key : ∀ᶠ n : ℕ in atTop, (n : ℝ) / (n + 1) = 1 - 1 / ((n : ℝ) + 1) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
        ring
      rw [tendsto_congr' key]
      have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
    have h2 : Tendsto (fun n : ℕ => (f x) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := f x)).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using (h1.mul tendsto_const_nhds).add h2
  have hbound : ∀ᶠ n in atTop,
      birkhoffAverage ℝ T f (n + 1) x < ((n : ℝ) / (n + 1)) * z + (f x) / (n + 1) := by
    filter_upwards [hev, eventually_gt_atTop 0] with n hn h0n
    rw [avg_succ_eq x n]
    have hmul' : ((n : ℝ) / (n + 1)) * birkhoffAverage ℝ T f n (T x) < ((n : ℝ) / (n + 1)) * z :=
      mul_lt_mul_of_pos_left hn (by positivity)
    linarith
  rcases eq_top_or_lt_top y with hytop | hytop
  · filter_upwards with n; rw [hytop]; exact le_top
  · have hybot : y ≠ ⊥ := fun h => by rw [h] at hzy; exact not_lt_bot hzy
    have hyr : y = (y.toReal : EReal) := (EReal.coe_toReal hytop.ne hybot).symm
    have hzyr : z < y.toReal := by rw [hyr] at hzy; exact_mod_cast hzy
    have hrlt : ∀ᶠ n : ℕ in atTop, ((n : ℝ) / (n + 1)) * z + (f x) / (n + 1) < y.toReal :=
      hr.eventually (eventually_lt_nhds hzyr)
    have hsucc : ∀ᶠ n in atTop, ((birkhoffAverage ℝ T f (n + 1) x : ℝ) : EReal) ≤ y := by
      filter_upwards [hbound, hrlt] with n hn1 hn2
      have hlt : birkhoffAverage ℝ T f (n + 1) x < y.toReal := lt_trans hn1 hn2
      rw [hyr]; exact_mod_cast hlt.le
    rw [eventually_atTop] at hsucc ⊢
    obtain ⟨N, hN⟩ := hsucc
    exact ⟨N + 1, fun m hm => by
      have := hN (m - 1) (by omega); rwa [Nat.sub_add_cancel (by omega)] at this⟩


end BirkhoffAE
end StatMech
