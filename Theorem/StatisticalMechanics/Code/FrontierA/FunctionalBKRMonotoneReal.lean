/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat.Part4
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneReal
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem layersFrom_map_fst (previous : ℝ) (levels : List ℝ) :
    (layersFrom previous levels).map Prod.fst = levels := by
  induction levels generalizing previous with
  | nil => rfl
  | cons a levels ih => simp [layersFrom, ih]

theorem fst_mem_of_mem_layersFrom {previous : ℝ} {levels : List ℝ}
    {layer : ℝ × ℝ} (hlayer : layer ∈ layersFrom previous levels) :
    layer.1 ∈ levels := by
  rw [<- layersFrom_map_fst previous levels]
  exact List.mem_map.mpr ⟨layer, hlayer, rfl⟩

theorem layersFrom_increment_nonneg {previous : ℝ} {levels : List ℝ}
    (hsorted : levels.Pairwise (· < ·))
    (hprevious : ∀ a ∈ levels, previous ≤ a) {layer : ℝ × ℝ}
    (hlayer : layer ∈ layersFrom previous levels) : 0 ≤ layer.2 := by
  induction levels generalizing previous layer with
  | nil => simp [layersFrom] at hlayer
  | cons a levels ih =>
      have hsorted' := List.pairwise_cons.mp hsorted
      simp only [layersFrom, List.mem_cons] at hlayer
      rcases hlayer with rfl | hlayer
      · exact sub_nonneg.mpr (hprevious a (by simp))
      · exact ih hsorted'.2 (fun b hb => (hsorted'.1 b hb).le) hlayer

theorem layersFrom_sum_eq_of_mem {previous target : ℝ} {levels : List ℝ}
    (hsorted : levels.Pairwise (· < ·))
    (hprevious : ∀ a ∈ levels, previous ≤ a) (hx : target ∈ levels) :
    previous +
        ((layersFrom previous levels).map fun layer =>
          if layer.1 ≤ target then layer.2 else 0).sum = target := by
  induction levels generalizing previous with
  | nil => simp at hx
  | cons a levels ih =>
      have hsorted' := List.pairwise_cons.mp hsorted
      rcases List.mem_cons.mp hx with htarget | hx
      · subst target
        have htail :
            ((layersFrom a levels).map fun layer =>
              if layer.1 ≤ a then layer.2 else 0).sum = 0 := by
          apply List.sum_eq_zero
          intro z hz
          obtain ⟨layer, hlayer, rfl⟩ := List.mem_map.mp hz
          have hlevel : layer.1 ∈ levels := fst_mem_of_mem_layersFrom hlayer
          simp [not_le_of_gt (hsorted'.1 layer.1 hlevel)]
        simp [layersFrom, htail]
      · have hax : a < target := hsorted'.1 target hx
        have htail := ih hsorted'.2 (fun b hb => (hsorted'.1 b hb).le) hx
        simp only [layersFrom, List.map_cons, List.sum_cons, if_pos hax.le]
        linarith


end StatMech.FrontierA
