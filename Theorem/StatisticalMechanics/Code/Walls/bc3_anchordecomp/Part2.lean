/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Def.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc3_corridorUnion_eq_pairwiseSeparated_wiring (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ ↔
      (¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) ∧
       ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) ∧
       ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) := Iff.rfl


theorem bc3_anchor_decomp_corridor (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) (x z : Site d)
    (h : Connected d (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω) x z) :
    Connected d ω x z ∨
      ∃ a ∈ bc3_anchorSites (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃), Connected d ω a z :=
  bc3_anchor_decomp _ ω x z h


theorem bc3_origin_mem_anchorSites_corridor (j : Fin d) (L : ℕ) :
    (0 : Site d) ∈ bc3_anchorSites (hrHD_corridorEdges j (L + 1)) := by
  refine ⟨s(hrHD_rayPt j (0 : ℤ), hrHD_rayPt j ((0 : ℤ) + 1)),
    hrHD_mem_corridorEdges (Nat.succ_pos L), ?_⟩
  have h0 : hrHD_rayPt j (0 : ℤ) = (0 : Site d) := by simp [hrHD_rayPt]
  rw [← h0]; exact Sym2.mem_mk_left _ _


theorem bc3_rayPt_mem_anchorSites_corridor (j : Fin d) (L t : ℕ) (ht : t < L) :
    hrHD_rayPt j ((t : ℤ) + 1) ∈ bc3_anchorSites (hrHD_corridorEdges j L) :=
  ⟨_, hrHD_mem_corridorEdges ht, Sym2.mem_mk_right _ _⟩


theorem bc3_anchorSites_corridorUnion_nonempty (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    (bc3_anchorSites (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃)).Nonempty := by
  refine ⟨0, ?_⟩
  obtain ⟨e, he, h0e⟩ := bc3_origin_mem_anchorSites_corridor j₁ L₁
  exact ⟨e, by
    rw [bc3_corridorUnion]
    exact (Finset.subset_union_left.trans Finset.subset_union_left) he, h0e⟩

end Walls
end StatMech
