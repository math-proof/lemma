/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc45depthwalk.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc46_openEdge_removeSite_of_ne (t : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : Site d} (htu : t ≠ u) (htv : t ≠ v) (h : IsOpenEdge d ω u v) :
    IsOpenEdge d (removeSite t ω) u v := by
  obtain ⟨hadj, hopen⟩ := h
  refine ⟨hadj, ?_⟩
  have hnotmem : t ∉ s(u, v) := by
    rw [Sym2.mem_iff]; push Not; exact ⟨htu, htv⟩
  rw [removeSite_apply_of_notMem hnotmem]; exact hopen


theorem bc46_armLink_survives (t : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    {x bx : Site d} (htx : t ≠ x) (htbx : t ≠ bx) (hedge : IsOpenEdge d ω x bx) :
    Connected d (removeSite t ω) x bx :=
  (bc46_openEdge_removeSite_of_ne t ω htx htbx hedge).connected


end StatMech.Walls
