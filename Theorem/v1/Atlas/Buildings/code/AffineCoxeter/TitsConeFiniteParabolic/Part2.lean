/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeFiniteParabolic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part3
import Mathlib.Order.Filter.Basic
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part2
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Translation between the two word-action conventions: $\sigma_w = \text{wordSigma}(w^R)$
where $w^R$ is the reversed word. -/
theorem sigmaWord_eq_wordSigma_reverse {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (ws : List B) (v : B → ℝ) :
    sigmaWord M ws v = CoxeterGroup.wordSigma M ws.reverse v := by
  induction ws generalizing v with
  | nil => simp [sigmaWord, CoxeterGroup.wordSigma]
  | cons r ws' ih =>
    simp only [sigmaWord, List.foldl_cons, List.reverse_cons]
    change sigmaWord M ws' (CoxeterGroup.sigma M r v) =
      CoxeterGroup.wordSigma M (ws'.reverse ++ [r]) v
    rw [ih (CoxeterGroup.sigma M r v)]
    rw [CoxeterGroup.wordSigma_append]
    simp [CoxeterGroup.wordSigma]

/-- A positive root $\alpha \neq e_s$ stays in $\Phi^+$ after applying $\sigma_s$.
The exception (the simple root $e_s$ itself) becomes $-e_s$, a negative root. -/
theorem sigma_preserves_pos {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (s : B) (α : B → ℝ)
    (hα : α ∈ standardΦpos M) (hne : α ≠ CoxeterGroup.e s) :
    CoxeterGroup.sigma M s α ∈ standardΦpos M := by
  obtain ⟨⟨ws, s₀, hα_eq⟩, hα_nn⟩ := hα
  constructor
  ·
    exact ⟨ws ++ [s], s₀, by rw [hα_eq]; simp [sigmaWord, List.foldl_append, List.foldl_cons, List.foldl_nil]⟩
  ·
    set cs := M.toCoxeterSystem

    have hα_ws : α = CoxeterGroup.wordSigma M ws.reverse (CoxeterGroup.e s₀) := by
      rw [hα_eq, sigmaWord_eq_wordSigma_reverse]

    have h_sigma_ws : CoxeterGroup.sigma M s α =
        CoxeterGroup.wordSigma M (s :: ws.reverse) (CoxeterGroup.e s₀) := by
      rw [hα_ws]; rfl

    set w := cs.wordProd (s :: ws.reverse)
    obtain ⟨rw, hrw_red, hrw_prod⟩ := cs.exists_reduced_word w

    have h_wordsigma_eq : ∀ (v : B → ℝ),
        CoxeterGroup.wordSigma M (s :: ws.reverse) v =
        CoxeterGroup.wordSigma M rw v :=
      fun v => CoxeterGroup.wordSigma_eq_of_wordProd_eq M cs _ _ hrw_prod v

    by_cases hasc : cs.length (cs.wordProd rw * cs.simple s₀) > cs.length (cs.wordProd rw)
    ·
      have hpos := CoxeterGroup.pos_of_ascent M cs rw s₀ hrw_red hasc
      rw [h_sigma_ws]
      intro t
      have h := congr_fun (h_wordsigma_eq (CoxeterGroup.e s₀)) t
      rw [h]; exact hpos t
    ·
      push_neg at hasc
      have hdesc : cs.length (cs.wordProd rw * cs.simple s₀) < cs.length (cs.wordProd rw) := by
        have := cs.length_mul_simple (cs.wordProd rw) s₀; omega
      have hneg := CoxeterGroup.neg_of_descent M cs rw s₀ hrw_red hdesc


      have hα_zero : ∀ t, t ≠ s → α t = 0 := by
        intro t hts
        have hle : CoxeterGroup.wordSigma M (s :: ws.reverse) (CoxeterGroup.e s₀) t ≤ 0 := by
          rw [congr_fun (h_wordsigma_eq (CoxeterGroup.e s₀)) t]; exact hneg t
        rw [← h_sigma_ws] at hle
        have hsigma_t : CoxeterGroup.sigma M s α t = α t := by
          simp only [CoxeterGroup.sigma, CoxeterGroup.bilinForm, CoxeterGroup.e, Pi.single_apply]
          have hst : s ≠ t := fun h => hts h.symm
          have hts' : t ≠ s := fun h => hts (h ▸ rfl)
          simp only [hts', ite_false, mul_zero, sub_zero]
        rw [hsigma_t] at hle
        exact le_antisymm hle (hα_nn t)

      have hα_form : CoxeterGroup.bilinForm M α α = 1 := by
        rw [hα_ws, CoxeterGroup.wordSigma_preserves_form,
            CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]

      have hα_eq_smul : α = α s • CoxeterGroup.e s := by
        ext t
        simp only [Pi.smul_apply, smul_eq_mul, CoxeterGroup.e, Pi.single_apply]
        by_cases hts : t = s
        · subst hts; simp
        · rw [hα_zero t hts]; simp [hts]

      have hα_form2 : CoxeterGroup.bilinForm M α α = α s * α s := by
        conv_lhs => rw [hα_eq_smul]
        rw [CoxeterGroup.bilinForm_smul_left, CoxeterGroup.bilinForm_smul_right,
            CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]; ring

      have hαs : α s = 1 := by
        have hmul : α s * α s = 1 := by linarith [hα_form, hα_form2]
        have hnn := hα_nn s
        nlinarith [sq_nonneg (α s - 1)]

      exfalso; apply hne
      rw [hα_eq_smul, hαs, one_smul]

end TitsCone
