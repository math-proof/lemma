/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Set.Finite.List

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup TitsCone

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The iterated dual-sigma word action: applying $\sigma_{s_1}^* \sigma_{s_2}^* \cdots$
in left-to-right order. This is the "co-action" version of the reflection action. -/
noncomputable def wordAction (M : CoxeterMatrix B) (ws : List B) (y : B → ℝ) : B → ℝ :=
  ws.foldl (fun v s => dualSigma M s v) y

/-- The empty word acts as the identity. -/
@[simp] theorem wordAction_nil (M : CoxeterMatrix B) (y : B → ℝ) :
    wordAction M [] y = y := rfl

/-- Cons step: prepending $s$ to the word means first applying the dual sigma at $s$. -/
theorem wordAction_cons (M : CoxeterMatrix B) (s : B) (ws : List B) (y : B → ℝ) :
    wordAction M (s :: ws) y = wordAction M ws (dualSigma M s y) :=
  List.foldl_cons ..

/-- Concatenation: the word action is the composition $\sigma^*_{ws_2} \circ \sigma^*_{ws_1}$. -/
theorem wordAction_append (M : CoxeterMatrix B) (ws₁ ws₂ : List B) (y : B → ℝ) :
    wordAction M (ws₁ ++ ws₂) y = wordAction M ws₂ (wordAction M ws₁ y) :=
  List.foldl_append ..

/-- Singleton word action: $\sigma^*_s$ applied to $y$. -/
theorem wordAction_singleton (M : CoxeterMatrix B) (s : B) (y : B → ℝ) :
    wordAction M [s] y = dualSigma M s y := rfl

/-- Applying the reverse word cancels: $\sigma^*_{\overline{ws}} \circ \sigma^*_{ws} = \mathrm{id}$. -/
theorem wordAction_reverse_cancel (M : CoxeterMatrix B) (ws : List B) (y : B → ℝ) :
    wordAction M ws.reverse (wordAction M ws y) = y := by
  induction ws generalizing y with
  | nil => rfl
  | cons s ws ih =>
    rw [wordAction_cons, List.reverse_cons, wordAction_append, wordAction_singleton]
    rw [ih]; exact dualSigma_involutive M s y

/-- Symmetric cancellation: $\sigma^*_{ws} \circ \sigma^*_{\overline{ws}} = \mathrm{id}$. -/
theorem wordAction_cancel_reverse (M : CoxeterMatrix B) (ws : List B) (y : B → ℝ) :
    wordAction M ws (wordAction M ws.reverse y) = y := by
  have h := wordAction_reverse_cancel M ws.reverse y
  rwa [List.reverse_reverse] at h

/-- $\sigma^*_s$ is $\mathbb{R}$-linear in the input. -/
theorem dualSigma_linear (M : CoxeterMatrix B) (s : B) (a b : ℝ) (x y : B → ℝ) :
    dualSigma M s (fun t => a * x t + b * y t) =
    fun t => a * dualSigma M s x t + b * dualSigma M s y t := by
  ext t; simp only [dualSigma]; ring

/-- The iterated word action is $\mathbb{R}$-linear: composition of linear maps. -/
theorem wordAction_linear (M : CoxeterMatrix B) (ws : List B) (a b : ℝ) (x y : B → ℝ) :
    wordAction M ws (fun t => a * x t + b * y t) =
    fun t => a * wordAction M ws x t + b * wordAction M ws y t := by
  induction ws generalizing x y with
  | nil => simp [wordAction]
  | cons s ws ih => rw [wordAction_cons, dualSigma_linear, wordAction_cons, wordAction_cons]; exact ih ..

/-- The Tits cone is closed under the dual word action: $\sigma^*_w$ sends
$\mathcal U$ to itself. -/
theorem titsConeSet_wordAction_closed (M : CoxeterMatrix B) (ws : List B) (x : B → ℝ)
    (hx : x ∈ titsConeSet M) : wordAction M ws x ∈ titsConeSet M := by
  obtain ⟨y, hy, ws', rfl⟩ := hx
  exact ⟨y, hy, ws' ++ ws, (wordAction_append M ws' ws y).symm⟩

/-- The simple reflection $\sigma_s^*$ fixes any vector lying on the wall
$\nu_s = 0$. -/
theorem dualSigma_fixed_on_wall (M : CoxeterMatrix B) (s : B) (ν : B → ℝ)
    (hν : ν s = 0) : dualSigma M s ν = ν := by
  ext t; simp only [dualSigma]; rw [hν]; ring

/-- Transpose identity: $\langle \sigma_s^* y, v\rangle = \langle y, \sigma_s v\rangle$,
expressing that $\sigma$ and $\sigma^*$ are mutually adjoint. -/
theorem dualSigma_sigma_transpose (M : CoxeterMatrix B) (s : B) (y v : B → ℝ) :
    ∑ t : B, (dualSigma M s y) t * v t = ∑ t : B, y t * (sigma M s v) t := by

  simp only [dualSigma, sigma]

  have hbf : bilinForm M v (e s) = ∑ i : B, v i * formVal M i s := by
    simp only [bilinForm]
    congr 1; ext i
    rw [Finset.sum_eq_single s]
    · simp [e, Pi.single]
    · intro j _ hj; simp [e, Pi.single, hj]
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [hbf]


  have lhs_eq : ∑ t : B, (y t - 2 * y s * formVal M s t) * v t =
      ∑ t : B, y t * v t - 2 * y s * ∑ t : B, formVal M s t * v t := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; ext t; ring
  have rhs_eq : ∑ t : B, y t * (v t - 2 * (∑ i : B, v i * formVal M i s) * (e s) t) =
      ∑ t : B, y t * v t - 2 * y s * ∑ i : B, v i * formVal M i s := by

    have : ∑ t : B, y t * (v t - 2 * (∑ i : B, v i * formVal M i s) * (e s) t) =
        ∑ t : B, (y t * v t - y t * (2 * (∑ i : B, v i * formVal M i s) * (e s) t)) := by
      congr 1; ext t; ring
    rw [this, Finset.sum_sub_distrib]
    congr 1

    have sum_indicator : ∑ t : B, y t * (2 * (∑ i : B, v i * formVal M i s) * (e s) t) =
        2 * y s * ∑ i : B, v i * formVal M i s := by
      rw [show (2 : ℝ) * y s * ∑ i : B, v i * formVal M i s =
          y s * (2 * (∑ i : B, v i * formVal M i s) * 1) by ring]
      rw [Finset.sum_eq_single s]
      · simp [e, Pi.single]
      · intro t _ ht; simp [e, Pi.single, ht]
      · intro h; exact absurd (Finset.mem_univ s) h
    exact sum_indicator
  rw [lhs_eq, rhs_eq]
  congr 1
  congr 1
  congr 1; ext t
  rw [formVal_symm M s t]; ring

/-- Coordinate formula via transpose: $(\sigma^*_w y)(s) = \sum_t y_t \cdot
(\sigma_w e_s)_t$. -/
theorem wordAction_transpose (M : CoxeterMatrix B) (ws : List B) (y : B → ℝ) (s : B) :
    wordAction M ws y s = ∑ t : B, y t * wordSigma M ws (e s) t := by
  induction ws generalizing y with
  | nil =>
    simp only [wordAction, wordSigma]


    simp only [e, Pi.single, Function.update, eq_comm]
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ ht; simp [show s ≠ t from Ne.symm ht]
    · intro h; exact absurd (Finset.mem_univ s) h
  | cons a rest ih =>
    rw [wordAction_cons, ih, wordSigma_cons]
    exact dualSigma_sigma_transpose M a y (wordSigma M rest (e s))

/-- The word action depends only on the group element $\mathrm{wordProd}(ws)$, not
on the word: two words representing the same Coxeter group element induce the
same dual word action. -/
theorem wordAction_eq_of_wordProd_eq (M : CoxeterMatrix B)
    (ws₁ ws₂ : List B) (h : M.toCoxeterSystem.wordProd ws₁ = M.toCoxeterSystem.wordProd ws₂)
    (y : B → ℝ) :
    wordAction M ws₁ y = wordAction M ws₂ y := by
  ext s
  rw [wordAction_transpose, wordAction_transpose]
  congr 1; ext t; congr 1
  exact congr_fun (wordSigma_eq_of_wordProd_eq M M.toCoxeterSystem ws₁ ws₂ h (e s)) t

/-- Descent detection: if the dual word action sends a nonnegative vector to a
vector with a negative $s$-coordinate, then $s$ is a right descent of the group
element $\mathrm{wordProd}(ws)$. -/
theorem isRightDescent_of_wordAction_neg (M : CoxeterMatrix B)
    (ws : List B) (y : B → ℝ) (hy : ∀ t, y t ≥ 0) (s : B)
    (hneg : wordAction M ws y s < 0) :
    M.toCoxeterSystem.IsRightDescent (M.toCoxeterSystem.wordProd ws) s := by
  set cs := M.toCoxeterSystem
  by_contra hasc_neg
  rw [CoxeterSystem.IsRightDescent] at hasc_neg
  push_neg at hasc_neg

  have hasc : cs.length (cs.wordProd ws * cs.simple s) > cs.length (cs.wordProd ws) := by
    have := cs.length_mul_simple (cs.wordProd ws) s; omega

  obtain ⟨rw, hrw_red, hrw_prod⟩ := cs.exists_reduced_word (cs.wordProd ws)

  have hrw_asc : cs.length (cs.wordProd rw * cs.simple s) > cs.length (cs.wordProd rw) := by
    rw [← hrw_prod]; exact hasc
  have hpos := CoxeterGroup.pos_of_ascent M cs rw s hrw_red hrw_asc

  have hσeq : ∀ t, wordSigma M ws (e s) t = wordSigma M rw (e s) t := by
    intro t
    exact congr_fun (wordSigma_eq_of_wordProd_eq M cs ws rw hrw_prod (e s)) t

  rw [wordAction_transpose] at hneg
  have hge : ∑ t : B, y t * wordSigma M ws (e s) t ≥ 0 :=
    Finset.sum_nonneg (fun t _ => mul_nonneg (hy t) (by rw [hσeq t]; exact hpos t))
  linarith

/-- Geometric exchange condition: when $(\sigma^*_w y)(s) < 0$ for $y \ge 0$,
the vector $\sigma_s^*(\sigma^*_w y)$ can be re-expressed via a shorter word $ws'$,
shrinking word length via the strong exchange property. -/
theorem exchange_condition (M : CoxeterMatrix B) :
  ∀ (ws : List B) (y : B → ℝ), (∀ s, y s ≥ 0) →
  ∀ (s : B), wordAction M ws y s < 0 →
  ∃ (ws' : List B) (y' : B → ℝ),
    ws'.length < ws.length ∧ (∀ s, y' s ≥ 0) ∧
    dualSigma M s (wordAction M ws y) = wordAction M ws' y' := by
  sorry

/-- The wall parameter $t_0 = \min_{s \in \mathrm{neg\_set}} \frac{x_s}{x_s - \mu_s}$:
the smallest $t \in [0,1]$ for which the convex combination $(1-t)x + t\mu$ reaches
the wall $\{z : z_s = 0\}$ for some $s$. -/
noncomputable def wallParam (x μ : B → ℝ) (neg_set : Finset B)
    (hne : neg_set.Nonempty) (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) : ℝ :=
  (neg_set.image (fun s => x s / (x s - μ s))).min' (hne.image _)

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

/-- The face $w \cdot F_I = \sigma^*_w(F_I)$: image of the standard face indexed by $I \subseteq S$
under the word action of $w$. -/
def wordFace (M : CoxeterMatrix B) (ws : List B) (I : Finset B) : Set (B → ℝ) :=
  (wordAction M ws) '' (titsFaceDual M I)

end TitsCone
