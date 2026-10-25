/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnGapAnalysis.Part2
import Lemma.List.InsertIdx.eq.Take.of.Le_Length
import Mathlib.LinearAlgebra.Dimension.Finite
import Def.v1.Atlas.Buildings.code.SphericalBuilding.FinsetGapCorrespondenceProof


namespace GLnBuilding

section FrameCorrespondence

variable (k : Type*) [Field k] (n : ℕ)

/-- For an $F$-compatible $V$, the extracted finset $S$ satisfies $V = \bigoplus_{i \in S} F.\mathrm{lines}\ i$. -/
theorem extractFinset_spec (F : Frame k n) (V : Submodule k (Vec k n))
    (hcompat : F.IsCompatible k n V) :
    V = ⨆ i ∈ extractFinset k n F V, F.lines i := by
  simp only [extractFinset, dif_pos hcompat]
  exact Classical.choose_spec hcompat

/-- $\bigoplus_{i \in S_1} L_i \le \bigoplus_{i \in S_2} L_i$ when $S_1 \subseteq S_2$. -/
theorem biSup_subset_le (F : Frame k n) (S₁ S₂ : Finset (Fin n)) (h : S₁ ⊆ S₂) :
    (⨆ i ∈ S₁, F.lines i) ≤ (⨆ i ∈ S₂, F.lines i) := by
  apply iSup_le_iSup_of_subset
  intro i hi
  exact h hi

/-- If $j \notin S_1$, then $F.\mathrm{lines}\ j$ is not contained in $\bigoplus_{i \in S_1} L_i$,
by the frame's independence. -/
theorem frame_line_not_le_biSup (F : Frame k n) (S₁ : Finset (Fin n))
    {j : Fin n} (hj : j ∉ S₁) :
    ¬(F.lines j ≤ ⨆ i ∈ S₁, F.lines i) := by
  intro hle
  have hindep := F.indep
  have hdisj := hindep.disjoint_biSup (Finset.mem_coe.not.mpr hj)
  have hbot : F.lines j = ⊥ := hdisj.eq_bot_of_le hle
  have h1 := F.one_dim j
  rw [hbot, finrank_bot] at h1
  omega

/-- Strict subset $S_1 \subsetneq S_2$ lifts to strict containment of frame-spans. -/
theorem frame_biSup_ssubset (F : Frame k n) {S₁ S₂ : Finset (Fin n)} (h : S₁ ⊂ S₂) :
    (⨆ i ∈ S₁, F.lines i) < (⨆ i ∈ S₂, F.lines i) := by
  apply lt_of_le_of_ne
  · exact biSup_subset_le k n F S₁ S₂ h.1
  · intro heq
    obtain ⟨j, hj2, hj1⟩ := Finset.exists_of_ssubset h
    have : F.lines j ≤ ⨆ i ∈ S₂, F.lines i :=
      le_iSup₂_of_le j hj2 (le_refl _)
    rw [← heq] at this
    exact frame_line_not_le_biSup k n F S₁ hj1 this

/-- A non-empty index set $S$ produces a non-zero frame-span. -/
theorem frame_biSup_ne_bot (F : Frame k n) {S : Finset (Fin n)} (hne : S.Nonempty) :
    (⨆ i ∈ S, F.lines i) ≠ ⊥ := by
  obtain ⟨j, hj⟩ := hne
  intro h
  have : F.lines j ≤ ⨆ i ∈ S, F.lines i :=
    le_iSup₂_of_le j hj (le_refl _)
  rw [h] at this
  have hbot : F.lines j = ⊥ := le_bot_iff.mp this
  have := F.one_dim j; rw [hbot, finrank_bot] at this; omega

/-- A proper index set $S \ne \mathrm{Finset.univ}$ produces a proper frame-span. -/
theorem frame_biSup_ne_top (F : Frame k n) {S : Finset (Fin n)} (hne : S ≠ Finset.univ) :
    (⨆ i ∈ S, F.lines i) ≠ ⊤ := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  have : F.lines j ≤ ⨆ i ∈ S, F.lines i := by
    rw [h]; exact le_top
  exact frame_line_not_le_biSup k n F S hj this

/-- Distinct index sets produce distinct frame-spans (injectivity of $S \mapsto \bigoplus_{i \in S} L_i$). -/
theorem frame_biSup_injective (F : Frame k n) {S₁ S₂ : Finset (Fin n)} (hne : S₁ ≠ S₂) :
    (⨆ i ∈ S₁, F.lines i) ≠ (⨆ i ∈ S₂, F.lines i) := by
  intro heq

  have : (∃ a, a ∈ S₁ ∧ a ∉ S₂) ∨ (∃ a, a ∈ S₂ ∧ a ∉ S₁) := by
    by_contra hh
    push_neg at hh
    exact hne (Finset.ext (fun x => ⟨fun h1 => hh.1 x h1, fun h2 => hh.2 x h2⟩))
  rcases this with ⟨j, hj1, hj2⟩ | ⟨j, hj2, hj1⟩
  · have : F.lines j ≤ ⨆ i ∈ S₁, F.lines i :=
      le_iSup₂_of_le j hj1 (le_refl _)
    rw [heq] at this
    exact frame_line_not_le_biSup k n F S₂ hj2 this
  · have : F.lines j ≤ ⨆ i ∈ S₂, F.lines i :=
      le_iSup₂_of_le j hj2 (le_refl _)
    rw [← heq] at this
    exact frame_line_not_le_biSup k n F S₁ hj1 this

end FrameCorrespondence
end GLnBuilding
