/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerBound.Part2


namespace StatMech.Onsager.CellEulerBound

open Finset SimpleGraph

open StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


def openTopSkeleton (S : Finset Cell) : SimpleGraph {v // v ∈ regVerts S} where
  Adj a b := s(a.1, b.1) ∈ regEdges S \ topEdges S
  symm := by
    constructor
    intro a b h
    rwa [Sym2.eq_swap]
  loopless := ⟨by
    intro a h
    exact (wad_edge_not_diag (mem_sdiff.mp h).1) (by simp)⟩

end StatMech.Onsager.CellEulerBound
