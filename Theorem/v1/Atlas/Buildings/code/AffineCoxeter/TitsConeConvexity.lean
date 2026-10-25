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
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

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

end TitsCone
