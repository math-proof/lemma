/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

@[simp]
theorem mem_annulus {n N : ℕ} {x : Site 2} :
    x ∈ annulus n N ↔ x ∈ box 2 N ∧ x ∉ box 2 n := Iff.rfl


theorem annulus_subset_box (n N : ℕ) : annulus n N ⊆ box 2 N := Set.diff_subset


theorem annulus_disjoint_inner (n N : ℕ) : Disjoint (annulus n N) (box 2 n) :=
  Set.disjoint_sdiff_left


theorem annulus_finite (n N : ℕ) : (annulus n N).Finite :=
  (box_finite 2 N).subset (annulus_subset_box n N)


theorem annulus_empty_of_le (N : ℕ) : annulus N N = ∅ := by
  simp [annulus]


theorem openSubgraph_mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω') :
    openSubgraph 2 ω ≤ openSubgraph 2 ω' := by
  intro x y hxy
  refine ⟨hxy.1, ?_⟩
  have hle := h s(x, y)
  rw [hxy.2] at hle
  exact top_le_iff.mp hle


end BeffaraDC
end StatMech
