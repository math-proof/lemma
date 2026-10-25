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
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.FinsetGapCorrespondenceProof.Part2


namespace GLnBuilding

section FrameCorrespondence

variable (k : Type*) [Field k] (n : ℕ)

/-- Proof of `FrameFinsetCorrespondenceHyp`: bundle the bijection between $F$-compatible
subspaces and subsets of $\mathrm{Fin}\ n$ via `extractFinset` and $S \mapsto \bigoplus_{i \in S} L_i$. -/
noncomputable def frameFinsetCorrespondenceHyp : FrameFinsetCorrespondenceHyp k n where
  extract := extractFinset k n
  extract_eq := fun F V hcompat => extractFinset_spec k n F V hcompat
  extract_ssubset := fun F V₁ V₂ hcompat₁ hcompat₂ hlt => by
    have heq₁ := extractFinset_spec k n F V₁ hcompat₁
    have heq₂ := extractFinset_spec k n F V₂ hcompat₂
    set S₁ := extractFinset k n F V₁
    set S₂ := extractFinset k n F V₂
    by_contra h

    by_cases hsub : S₁ ⊆ S₂
    ·
      have heqs : S₁ = S₂ := by
        rw [Finset.ssubset_iff_subset_ne] at h; push_neg at h
        exact h hsub
      rw [heq₁, heq₂, heqs] at hlt
      exact lt_irrefl _ hlt
    ·
      obtain ⟨j, hj1, hj2⟩ := Finset.not_subset.mp hsub
      have hle : F.lines j ≤ ⨆ i ∈ S₂, F.lines i := by
        calc F.lines j ≤ ⨆ i ∈ S₁, F.lines i :=
              le_iSup₂_of_le j hj1 (le_refl _)
          _ = V₁ := heq₁.symm
          _ ≤ V₂ := hlt.le
          _ = ⨆ i ∈ S₂, F.lines i := heq₂
      exact frame_line_not_le_biSup k n F S₂ hj2 hle
  extract_nonempty := fun F V hcompat hbot => by
    rw [extractFinset_spec k n F V hcompat] at hbot
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hbot
    simp at hbot
  extract_proper := fun F V hcompat htop => by
    rw [extractFinset_spec k n F V hcompat] at htop
    intro h; apply htop
    rw [h]
    simp [F.spanning]
  lift_ssubset := fun F S₁ S₂ h => frame_biSup_ssubset k n F h
  lift_nonempty := fun F S hne => frame_biSup_ne_bot k n F hne
  lift_proper := fun F S hpr => frame_biSup_ne_top k n F hpr
  lift_ne := fun F S₁ S₂ hne => frame_biSup_injective k n F hne

end FrameCorrespondence
end GLnBuilding
