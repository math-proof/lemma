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
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part3
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Construction of `RootSystemData` from the standard positive roots, given the two
finiteness hypotheses encapsulated in `FiniteProperParabolicsHyp`. -/
noncomputable def rootSystemData_standard (M : CoxeterMatrix B)
    (hfpp : FiniteProperParabolicsHyp M) :
    RootSystemData M where
  Φpos := standardΦpos M
  roots_in_subspan_finite := fun I hI => hfpp.finiteRoots_in_subspan_of_subset_finite I hI
  pos_pairing_outside_span := by
    intro I x hx α hα hexists
    obtain ⟨_, hα_nn⟩ := hα
    obtain ⟨hx_zero, hx_pos⟩ := hx
    obtain ⟨s₀, hs₀_notI, hs₀_ne⟩ := hexists
    unfold pairing
    apply Finset.sum_pos'
    · intro i _
      apply mul_nonneg (hα_nn i)
      by_cases hi : i ∈ I
      · rw [hx_zero i hi]
      · exact le_of_lt (hx_pos i hi)
    · exact ⟨s₀, Finset.mem_univ s₀,
        mul_pos (lt_of_le_of_ne (hα_nn s₀) (Ne.symm hs₀_ne))
          (hx_pos s₀ hs₀_notI)⟩
  pairing_word_comm := fun ws α x => pairing_word_comm_lemma M ws α x
  sigmaWord_injective := fun ws => sigmaWord_injective_lemma M ws
  inversions_finite := by
    intro ws
    induction ws using List.reverseRecOn with
    | nil =>

      convert Set.finite_empty
      ext α; simp [standardΦpos, sigmaWord]
    | append_singleton ws' s ih =>
      exact inversions_append_finite M ws' s ih
  simple_inversion := by
    intro s
    ext α
    simp only [Set.mem_sep_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hα_pos, hα_not⟩

      simp only [sigmaWord, List.foldl_cons, List.foldl_nil] at hα_not
      by_contra hne
      exact hα_not (sigma_preserves_pos M s α hα_pos hne)
    · intro h; subst h
      exact e_mem_inversion_singleton M s
  nonposRoots_finite_on_hyperplane :=
    fun v₀ hv₀_pos hv₀_rad x hx =>
      hfpp.hyperplane_nonposRoots_finite v₀ hv₀_pos hv₀_rad x hx

end TitsCone
