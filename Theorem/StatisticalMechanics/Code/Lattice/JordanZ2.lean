/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Def.StatisticalMechanics.Code.Lattice.JordanZ2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem faceAdj_bottom (a b : ℤ) :
    (hypercubicLattice 2).Adj (faceCorner00 a b) (faceCorner10 a b) := by
  simp [faceCorner00, faceCorner10, hypercubicLattice_adj, Fin.sum_univ_two]


theorem faceAdj_right (a b : ℤ) :
    (hypercubicLattice 2).Adj (faceCorner10 a b) (faceCorner11 a b) := by
  simp [faceCorner10, faceCorner11, hypercubicLattice_adj, Fin.sum_univ_two]


theorem faceAdj_top (a b : ℤ) :
    (hypercubicLattice 2).Adj (faceCorner11 a b) (faceCorner01 a b) := by
  simp [faceCorner11, faceCorner01, hypercubicLattice_adj, Fin.sum_univ_two]


theorem faceAdj_left (a b : ℤ) :
    (hypercubicLattice 2).Adj (faceCorner01 a b) (faceCorner00 a b) := by
  simp [faceCorner01, faceCorner00, hypercubicLattice_adj, Fin.sum_univ_two]


end Lattice
end StatMech
