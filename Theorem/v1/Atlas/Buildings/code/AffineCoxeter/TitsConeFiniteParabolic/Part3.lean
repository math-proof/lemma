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
import Structure.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Appending one letter: $\sigma_{w \cdot s}(\alpha) = \sigma_s(\sigma_w(\alpha))$. -/
theorem sigmaWord_append_singleton (M : CoxeterMatrix B) (ws : List B) (s : B) (α : B → ℝ) :
    sigmaWord M (ws ++ [s]) α = CoxeterGroup.sigma M s (sigmaWord M ws α) := by
  simp [sigmaWord, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Inductive step for the finiteness of inversion sets: if the inversion set of $w$ is
finite, so is the inversion set of $w \cdot s$. -/
theorem inversions_append_finite (M : CoxeterMatrix B) (ws : List B) (s : B)
    (ih : Set.Finite {α ∈ standardΦpos M | sigmaWord M ws α ∉ standardΦpos M}) :
    Set.Finite {α ∈ standardΦpos M | sigmaWord M (ws ++ [s]) α ∉ standardΦpos M} := by


  have hsingle : Set.Finite {α ∈ standardΦpos M | sigmaWord M ws α = CoxeterGroup.e s} := by
    have : {α ∈ standardΦpos M | sigmaWord M ws α = CoxeterGroup.e s} ⊆
        sigmaWord M ws ⁻¹' {CoxeterGroup.e s} :=
      fun α ⟨_, h⟩ => Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr h)
    exact Set.Finite.subset
      ((Set.finite_singleton _).preimage (Set.injOn_of_injective (sigmaWord_injective_lemma M ws)
        |>.mono (Set.subset_univ _))) this
  apply Set.Finite.subset (ih.union hsingle)
  intro α ⟨hα_pos, hα_not⟩
  rw [sigmaWord_append_singleton] at hα_not
  by_cases h : sigmaWord M ws α ∈ standardΦpos M
  ·
    right
    refine ⟨hα_pos, ?_⟩
    by_contra hne
    exact hα_not (sigma_preserves_pos M s _ h hne)
  ·
    left
    exact ⟨hα_pos, h⟩

/-- The simple root $e_s$ is positive but $\sigma_s(e_s) = -e_s$ is not in $\Phi^+$:
the unique inversion of the simple reflection $s$ is $e_s$. -/
theorem e_mem_inversion_singleton (M : CoxeterMatrix B) (s : B) :
    CoxeterGroup.e s ∈ standardΦpos M ∧
    sigmaWord M [s] (CoxeterGroup.e s) ∉ standardΦpos M := by
  constructor
  ·
    constructor
    · exact ⟨[], s, rfl⟩
    · intro t; simp [CoxeterGroup.e, Pi.single_apply]; split <;> norm_num
  ·
    simp only [sigmaWord, List.foldl_cons, List.foldl_nil]
    intro ⟨_, hnn⟩
    have h1 := hnn s
    have h2 := CoxeterGroup.sigma_e_self M s

    have : CoxeterGroup.sigma M s (CoxeterGroup.e s) s = -1 := by
      rw [h2]; simp [CoxeterGroup.e, Pi.single_apply]
    linarith

end TitsCone
