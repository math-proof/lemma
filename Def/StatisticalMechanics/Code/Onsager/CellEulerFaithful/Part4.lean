/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBoundary
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part3


namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


noncomputable def cellSkeletonEdgeEquiv (S : Finset Cell) :
    {e // e ∈ (cellSkeleton S).edgeSet} ≃ {e // e ∈ StatMech.Euc.regEdges S} where
  toFun e := ⟨Sym2.map Subtype.val e.1, by
    exact (mem_cellSkeleton_edgeSet_iff S e.1).mp e.2⟩
  invFun e := ⟨e.1.attachWith (fun v hv => wad_edge_mem_regVerts e.2 hv), by
    rw [mem_cellSkeleton_edgeSet_iff]
    simpa only [Sym2.attachWith_map_subtypeVal] using e.2⟩
  left_inv e := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    simp only [Sym2.attachWith_map_subtypeVal]
  right_inv e := by
    apply Subtype.ext
    simp only [Sym2.attachWith_map_subtypeVal]

end StatMech.Onsager.CellEulerFaithful
