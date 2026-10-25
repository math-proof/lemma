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
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part4


namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


def skeletonVertexOfCorner (S : Finset Cell) (c : Cell) (hc : c ∈ S)
    (v : Vtx) (hv : v ∈ StatMech.Euc.cellVerts c) : {v // v ∈ regVerts S} :=
  ⟨v, wad_cellVerts_subset_regVerts hc hv⟩


end StatMech.Onsager.CellEulerFaithful
