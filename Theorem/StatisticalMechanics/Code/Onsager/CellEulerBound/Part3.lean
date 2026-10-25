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
import Def.StatisticalMechanics.Code.Onsager.CellEulerBound.Part3


namespace StatMech.Onsager.CellEulerBound

open Finset SimpleGraph

open StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


theorem mem_openTopSkeleton_edgeSet_iff (S : Finset Cell)
    (e : Sym2 {v // v ∈ regVerts S}) :
    e ∈ (openTopSkeleton S).edgeSet ↔
      Sym2.map Subtype.val e ∈ regEdges S \ topEdges S := by
  induction e with
  | h a b => rfl


end StatMech.Onsager.CellEulerBound
