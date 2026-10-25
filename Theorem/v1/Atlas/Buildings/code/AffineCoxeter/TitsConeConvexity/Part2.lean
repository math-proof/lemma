/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Set.Finite.List
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part2
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The wall parameter is the minimum over the negative set, so it bounds each
individual ratio. -/
theorem wallParam_le_ratio (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) (s : B) (hs : s ∈ neg_set) :
    wallParam x μ neg_set hne hx hμ ≤ x s / (x s - μ s) :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)

/-- The wall parameter is attained: some $s_0 \in \mathrm{neg\_set}$ realises the
minimum ratio $x_{s_0} / (x_{s_0} - \mu_{s_0})$. -/
theorem wallParam_eq_some_ratio (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) :
    ∃ s₀ ∈ neg_set, wallParam x μ neg_set hne hx hμ = x s₀ / (x s₀ - μ s₀) := by
  have := Finset.min'_mem (neg_set.image (fun s => x s / (x s - μ s))) (hne.image _)
  rw [Finset.mem_image] at this
  obtain ⟨s₀, hs₀, heq⟩ := this
  exact ⟨s₀, hs₀, heq.symm⟩

/-- The wall parameter is nonnegative, since each individual ratio is. -/
theorem wallParam_nonneg (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) :
    0 ≤ wallParam x μ neg_set hne hx hμ := by
  apply Finset.le_min'
  intro r hr
  rw [Finset.mem_image] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  exact div_nonneg (hx s) (by linarith [hμ s hs, hx s])

/-- The wall parameter lies in $[0, 1]$: for each $s$ in the negative set
$x_s / (x_s - \mu_s) \le 1$ since $\mu_s < 0$. -/
theorem wallParam_le_one (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) :
    wallParam x μ neg_set hne hx hμ ≤ 1 := by
  have ⟨s₀, hs₀⟩ := hne
  calc wallParam x μ neg_set hne hx hμ
      ≤ x s₀ / (x s₀ - μ s₀) := wallParam_le_ratio x μ neg_set hne hx hμ s₀ hs₀
    _ ≤ 1 := by rw [div_le_one (by linarith [hμ s₀ hs₀, hx s₀])]; linarith [hμ s₀ hs₀]

/-- The wall point $(1-t_0)\,x + t_0\,\mu$ at the wall parameter has nonnegative
coordinates at every $s'$: at indices in the negative set the choice of $t_0$
keeps the coordinate $\ge 0$; at others both summands are nonnegative. -/
theorem wallPoint_nonneg (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ_neg : ∀ s ∈ neg_set, μ s < 0) (hμ_pos : ∀ s, s ∉ neg_set → μ s ≥ 0)
    (s' : B) :
    let t₀ := wallParam x μ neg_set hne hx hμ_neg
    (1 - t₀) * x s' + t₀ * μ s' ≥ 0 := by
  simp only
  set t₀ := wallParam x μ neg_set hne hx hμ_neg
  have ht₀_nn := wallParam_nonneg x μ neg_set hne hx hμ_neg
  have ht₀_le1 := wallParam_le_one x μ neg_set hne hx hμ_neg
  by_cases hs' : s' ∈ neg_set
  · have hd : x s' - μ s' > 0 := by linarith [hx s', hμ_neg s' hs']
    have ht₀_le : t₀ ≤ x s' / (x s' - μ s') := wallParam_le_ratio x μ neg_set hne hx hμ_neg s' hs'
    have : t₀ * (x s' - μ s') ≤ x s' := by
      calc t₀ * (x s' - μ s') ≤ x s' / (x s' - μ s') * (x s' - μ s') :=
              mul_le_mul_of_nonneg_right ht₀_le (le_of_lt hd)
        _ = x s' := div_mul_cancel₀ (x s') (ne_of_gt hd)
    linarith
  · apply add_nonneg
    · exact mul_nonneg (by linarith) (hx s')
    · exact mul_nonneg ht₀_nn (hμ_pos s' hs')

/-- The wall point hits zero at the minimising index: some $s_0$ has wall-point
coordinate equal to $0$. -/
theorem wallPoint_zero (x μ : B → ℝ) (neg_set : Finset B) (hne : neg_set.Nonempty)
    (hx : ∀ s, x s ≥ 0) (hμ_neg : ∀ s ∈ neg_set, μ s < 0) :
    ∃ s₀ ∈ neg_set,
      let t₀ := wallParam x μ neg_set hne hx hμ_neg
      (1 - t₀) * x s₀ + t₀ * μ s₀ = 0 := by
  obtain ⟨s₀, hs₀, ht₀_eq⟩ := wallParam_eq_some_ratio x μ neg_set hne hx hμ_neg
  refine ⟨s₀, hs₀, ?_⟩
  have hd : x s₀ - μ s₀ > 0 := by linarith [hx s₀, hμ_neg s₀ hs₀]
  simp only [ht₀_eq]
  field_simp
  ring

/-- Strong induction on word length: any convex combination of $x \in \mathcal D_0$
and $\sigma^*_w y$ (with $y$ nonneg) lies in the Tits cone. This is the key step
of convexity; the wall-parameter / exchange-condition machinery shrinks $|w|$. -/
theorem convex_closure_titsCone (M : CoxeterMatrix B) :
    ∀ (n : ℕ),
    ∀ (ws : List B), ws.length ≤ n →
    ∀ (y : B → ℝ), (∀ s, y s ≥ 0) →
    ∀ (x : B → ℝ), (∀ s, x s ≥ 0) →
    ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    (fun t => a * x t + b * wordAction M ws y t) ∈ titsConeSet M := by
  intro n
  induction n with
  | zero =>
    intro ws hlen y hy x hx a b ha hb hab
    have : ws = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst this; simp only [wordAction_nil]
    exact ⟨_, fun s => add_nonneg (mul_nonneg ha (hx s)) (mul_nonneg hb (hy s)), [], rfl⟩
  | succ n ih =>
    intro ws hlen y hy x hx a b ha hb hab
    set μ := wordAction M ws y with μ_def

    by_cases h_nn : ∀ s, a * x s + b * μ s ≥ 0
    · exact ⟨_, h_nn, [], rfl⟩
    · push_neg at h_nn
      obtain ⟨s_bad, hs_bad⟩ := h_nn

      have hμ_bad : μ s_bad < 0 := by
        by_contra h; push_neg at h
        linarith [mul_nonneg ha (hx s_bad), mul_nonneg hb h]

      have hb_pos : 0 < b := by
        by_contra h; push_neg at h
        have := le_antisymm h hb; subst this
        simp at hs_bad; linarith [mul_nonneg ha (hx s_bad)]

      set neg_set := Finset.univ.filter (fun s => μ s < 0) with neg_set_def
      have hne : neg_set.Nonempty := ⟨s_bad, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ_bad⟩⟩
      have hμ_neg : ∀ s ∈ neg_set, μ s < 0 := fun s hs => (Finset.mem_filter.mp hs).2
      have hμ_pos : ∀ s, s ∉ neg_set → μ s ≥ 0 := by
        intro s hs; rw [neg_set_def, Finset.mem_filter, not_and] at hs
        exact not_lt.mp (hs (Finset.mem_univ s))

      set t₀ := wallParam x μ neg_set hne hx hμ_neg
      have ht₀_nn := wallParam_nonneg x μ neg_set hne hx hμ_neg
      have ht₀_le1 := wallParam_le_one x μ neg_set hne hx hμ_neg

      set ν := fun t => (1 - t₀) * x t + t₀ * μ t with ν_def
      have hν_nn : ∀ s', ν s' ≥ 0 :=
        wallPoint_nonneg x μ neg_set hne hx hμ_neg hμ_pos

      obtain ⟨s₀, hs₀_mem, hν_zero⟩ := wallPoint_zero x μ neg_set hne hx hμ_neg
      have hμs₀ : μ s₀ < 0 := hμ_neg s₀ hs₀_mem

      have hb_gt_t₀ : t₀ < b := by
        by_contra h; push_neg at h


        have hd : x s_bad - μ s_bad > 0 := by linarith [hx s_bad]
        have : a * x s_bad + b * μ s_bad ≥ ν s_bad := by
          simp only [ν_def]; have ha_eq : a = 1 - b := by linarith
          rw [ha_eq]; nlinarith
        linarith [hν_nn s_bad]

      have ht₀_lt1 : t₀ < 1 := by linarith

      obtain ⟨ws', y', hlen', hy', hσ⟩ := exchange_condition M ws y hy s₀ hμs₀

      set c := (b - t₀) / (1 - t₀) with c_def
      have hc_nn : 0 ≤ c := div_nonneg (by linarith) (by linarith)
      have hc_le1 : c ≤ 1 := by rw [c_def, div_le_one (by linarith)]; linarith

      have hz_eq : (fun t => a * x t + b * μ t) = (fun t => (1 - c) * ν t + c * μ t) := by
        have h1t : (1 : ℝ) - t₀ ≠ 0 := by linarith
        ext t; simp only [ν_def, c_def]
        have ha_eq : a = 1 - b := by linarith
        rw [ha_eq]; field_simp; ring
      rw [hz_eq]

      have hσ_linear : dualSigma M s₀ (fun t => (1 - c) * ν t + c * μ t) =
          fun t => (1 - c) * ν t + c * (wordAction M ws' y') t := by
        rw [dualSigma_linear, dualSigma_fixed_on_wall M s₀ ν hν_zero, hσ]

      have h_refl_in_U :
          (fun t => (1 - c) * ν t + c * (wordAction M ws' y') t) ∈ titsConeSet M := by
        exact ih ws' (by omega) y' hy' ν hν_nn (1 - c) c (by linarith) hc_nn (by ring)


      have hσ_inv : dualSigma M s₀ (wordAction M ws' y') = μ := by
        rw [← hσ, dualSigma_involutive]
      have hinv : dualSigma M s₀ (fun t => (1 - c) * ν t + c * (wordAction M ws' y') t) =
          fun t => (1 - c) * ν t + c * μ t := by
        rw [dualSigma_linear, dualSigma_fixed_on_wall M s₀ ν hν_zero, hσ_inv]

      have h_in_U : (fun t => (1 - c) * ν t + c * μ t) ∈ titsConeSet M := by
        rw [← hinv]
        exact titsConeSet_wordAction_closed M [s₀] _ h_refl_in_U
      exact h_in_U

/-- The Tits cone $\mathcal U \subset (B \to \mathbb R)$ is convex. -/
theorem titsConeSet_convex (M : CoxeterMatrix B) :
    Convex ℝ (titsConeSet M) := by
  intro p hp q hq a b ha hb hab

  obtain ⟨y₁, hy₁, ws₁, hp_eq⟩ := hp
  obtain ⟨y₂, hy₂, ws₂, hq_eq⟩ := hq

  have hp' : p = wordAction M ws₁ y₁ := hp_eq
  have hq' : q = wordAction M ws₂ y₂ := hq_eq
  subst hp'; subst hq'

  have key : (fun t => a * y₁ t + b * wordAction M (ws₂ ++ ws₁.reverse) y₂ t) ∈ titsConeSet M :=
    convex_closure_titsCone M (ws₂ ++ ws₁.reverse).length (ws₂ ++ ws₁.reverse) (le_refl _)
      y₂ hy₂ y₁ hy₁ a b ha hb hab

  have hmapped := titsConeSet_wordAction_closed M ws₁ _ key

  show a • wordAction M ws₁ y₁ + b • wordAction M ws₂ y₂ ∈ titsConeSet M
  have heq : a • wordAction M ws₁ y₁ + b • wordAction M ws₂ y₂ =
      wordAction M ws₁ (fun t => a * y₁ t + b * wordAction M (ws₂ ++ ws₁.reverse) y₂ t) := by
    rw [wordAction_linear]
    have cancel_y₂ : wordAction M ws₁ (wordAction M (ws₂ ++ ws₁.reverse) y₂) =
        wordAction M ws₂ y₂ := by
      rw [wordAction_append]
      exact wordAction_cancel_reverse M ws₁ (wordAction M ws₂ y₂)
    ext t; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [congr_fun cancel_y₂.symm t]
  rw [heq]; exact hmapped

end TitsCone
