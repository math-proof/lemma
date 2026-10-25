/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingBridge.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Def.StatisticalMechanics.Code.Onsager.InteriorRegion.Part4


namespace StatMech.Onsager.InteriorRegion

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches

open StatMech.Onsager.WindingBridge


theorem wReflex_not_interior : toSite wReflex ∉ Lint := by
  rw [Lint, mem_liftS, mem_Lcells]
  simp only [wReflex]
  omega


theorem launch_pt_interior : toSite (wReflex.1 + 1, wReflex.2) ∈ Lint := by
  rw [Lint, mem_liftS, mem_Lcells]
  simp only [wReflex]
  omega


theorem launch_interior : toSite (rayX wReflex 1) ∈ Lint := by
  have : rayX wReflex 1 = (wReflex.1 + 1, wReflex.2) := by
    simp only [rayX, wReflex]; norm_num
  rw [this]; exact launch_pt_interior


theorem wReflex_mem_boundary : wReflex ∈ (mkBoxData Lint Lint_finite).B := by
  rw [mkBoxData, Set.Finite.mem_toFinset, Bset, Set.mem_setOf_eq, bdEdge_mk]
  constructor
  · intro h; exact absurd h wReflex_not_interior
  · intro h; exact absurd launch_pt_interior h


theorem wReflex_isReflex :
    cross (1, 0) (0, -1) = -1 ∧
      (cross (1, 0) (1, 0) = 0 ∧ 0 < cross (0, -1) (1, 0)) := by
  refine ⟨by decide, ?_⟩
  exact reflex_continuation_interior (1, 0) (0, -1) (Or.inl rfl) (by decide)


theorem wReflex_quadrant :
    (toSite (2, 1) ∈ Lint ∧ toSite (1, 2) ∈ Lint) ∧
      (toSite (0, 1) ∉ Lint ∧ toSite (1, 0) ∉ Lint) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    · rw [Lint, mem_liftS, mem_Lcells]; simp only; omega


theorem Lshape_interiorReaches :
    InteriorReaches (mkBoxData Lint Lint_finite) wReflex :=
  interiorReaches_of_cluster Lint Lint_finite wReflex launch_interior


theorem Lshape_chord :
    ∃ k : ℕ, 1 ≤ k ∧ rayX wReflex k ∈ (mkBoxData Lint Lint_finite).B ∧
      (∀ j : ℕ, 1 ≤ j → j < k → rayX wReflex j ∉ (mkBoxData Lint Lint_finite).B) :=
  chord_of_cluster Lint Lint_finite wReflex wReflex_mem_boundary launch_interior


end StatMech.Onsager.InteriorRegion
