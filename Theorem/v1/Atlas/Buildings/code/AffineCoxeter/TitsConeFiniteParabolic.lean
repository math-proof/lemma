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
import Class.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

theorem sigma_involutive (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    CoxeterGroup.sigma M s (CoxeterGroup.sigma M s v) = v := by
  ext t
  simp only [CoxeterGroup.sigma, CoxeterGroup.bilinForm, CoxeterGroup.e, Pi.single_apply]
  by_cases hts : s = t
  · subst hts

    simp only [ite_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
               Finset.mem_univ]


    simp_rw [sub_mul]
    simp only [Finset.sum_sub_distrib]

    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
               CoxeterGroup.formVal_diag, mul_one]
    ring
  ·
    have hts' : t ≠ s := fun h => hts (h ▸ rfl)
    simp only [hts', ite_false, mul_zero, sub_zero]

theorem sigma_injective (M : CoxeterMatrix B) (s : B) :
    Function.Injective (CoxeterGroup.sigma M s) := by
  intro a b hab
  have := congr_arg (CoxeterGroup.sigma M s) hab
  rwa [sigma_involutive, sigma_involutive] at this

theorem sigmaWord_cons (M : CoxeterMatrix B) (s : B) (ws' : List B) (α : B → ℝ) :
    sigmaWord M (s :: ws') α = sigmaWord M ws' (CoxeterGroup.sigma M s α) := by
  simp [sigmaWord, List.foldl_cons]

theorem sigmaWord_injective_lemma (M : CoxeterMatrix B) (ws : List B) :
    Function.Injective (sigmaWord M ws) := by
  induction ws with
  | nil => exact Function.injective_id
  | cons s ws' ih =>
    intro a b h
    rw [sigmaWord_cons, sigmaWord_cons] at h
    exact sigma_injective M s (ih h)

theorem pairing_dualSigma_eq_sigma_pairing (M : CoxeterMatrix B) (s : B) (α x : B → ℝ) :
    pairing α (dualSigma M s x) = pairing (CoxeterGroup.sigma M s α) x := by
  simp only [pairing, dualSigma, CoxeterGroup.sigma, CoxeterGroup.bilinForm,
             CoxeterGroup.e, Pi.single_apply]
  simp_rw [mul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_sub_distrib]

  congr 1


  simp only [ite_mul, zero_mul, mul_ite, mul_one, mul_zero,
             Finset.sum_ite_eq', Finset.mem_univ, ite_true]

  ring_nf
  simp_rw [CoxeterGroup.formVal_symm M s]
  simp_rw [show ∀ t : B, α t * x s * formVal M t s * 2 = x s * 2 * (α t * formVal M t s) from
    fun t => by ring]
  rw [← Finset.mul_sum]
  ring

theorem dualSigmaWord_cons (M : CoxeterMatrix B) (s : B) (ws' : List B) (x : B → ℝ) :
    dualSigmaWord M (s :: ws') x = dualSigmaWord M ws' (dualSigma M s x) := by
  simp [dualSigmaWord, List.foldl_cons]

theorem pairing_word_comm_lemma (M : CoxeterMatrix B) (ws : List B) (α x : B → ℝ) :
    pairing α (dualSigmaWord M ws x) = pairing (sigmaWord M ws.reverse α) x := by
  induction ws generalizing α x with
  | nil => rfl
  | cons s ws' ih =>
    rw [dualSigmaWord_cons, ih α (dualSigma M s x), List.reverse_cons]
    simp only [sigmaWord, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [pairing_dualSigma_eq_sigma_pairing]

end TitsCone
