/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
import Def.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bgn_sameTrif_classes_laminar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (u a b : Site d) :
    bgn_boundaryClass ω L R u a = bgn_boundaryClass ω L R u b ∨
      Disjoint (bgn_boundaryClass ω L R u a) (bgn_boundaryClass ω L R u b) := by
  by_cases h : (bkg_deleteVertex (bgn_Gn ω L) u).Reachable a b
  · left
    ext c
    simp only [bgn_boundaryClass, Set.mem_setOf_eq]
    exact ⟨fun ⟨hc, hac⟩ => ⟨hc, h.symm.trans hac⟩, fun ⟨hc, hbc⟩ => ⟨hc, h.trans hbc⟩⟩
  · right
    rw [Set.disjoint_left]
    rintro c ⟨_, hac⟩ ⟨_, hbc⟩
    exact h (hac.trans hbc.symm)


end StatMech.Walls
