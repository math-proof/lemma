/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanEnclosure
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem sharedPrimalEdge_right (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a + 1, b] = s(faceCorner10 a b, faceCorner11 a b) := by
  unfold sharedPrimalEdge faceCorner10 faceCorner11
  rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max a (a + 1) = a + 1 by omega]


theorem sharedPrimalEdge_left (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a - 1, b] = s(faceCorner00 a b, faceCorner01 a b) := by
  unfold sharedPrimalEdge faceCorner00 faceCorner01
  rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max a (a - 1) = a by omega]


theorem sharedPrimalEdge_top (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a, b + 1] = s(faceCorner01 a b, faceCorner11 a b) := by
  unfold sharedPrimalEdge faceCorner01 faceCorner11
  rw [if_pos (by simp only [Matrix.cons_val_zero])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max b (b + 1) = b + 1 by omega]


theorem sharedPrimalEdge_bottom (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a, b - 1] = s(faceCorner00 a b, faceCorner10 a b) := by
  unfold sharedPrimalEdge faceCorner00 faceCorner10
  rw [if_pos (by simp only [Matrix.cons_val_zero])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max b (b - 1) = b by omega]


end Lattice
end StatMech
