/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Def.StatisticalMechanics.Code.Lattice.EulerFaces.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem boxFaceCount_eq (n : ℕ) : boxFaceCount n = (2 * n) ^ 2 + 1 := by
  rw [boxFaceCount, boxCells_card]


theorem box_euler (n : ℕ) :
    (boxVerts n).card + boxFaceCount n = (boxEdges n).card + 2 := by
  rw [boxVerts_card, boxFaceCount_eq, boxEdges_card]
  ring


theorem box_euler_sub (n : ℕ) :
    ((boxVerts n).card : ℤ) - (boxEdges n).card + boxFaceCount n = 2 := by
  have h := box_euler n
  have : ((boxVerts n).card : ℤ) + (boxFaceCount n : ℤ) = ((boxEdges n).card : ℤ) + 2 := by
    exact_mod_cast h
  linarith


theorem box_faceCount_eq_cyclomatic_add_one (n : ℕ) :
    boxFaceCount n = (((boxEdges n).card + 1) - (boxVerts n).card) + 1 := by
  have h := box_euler n
  have hge : (boxVerts n).card ≤ (boxEdges n).card + 1 := by
    rw [boxVerts_card, boxEdges_card]; nlinarith [Nat.zero_le n]
  omega


end Lattice
end StatMech
