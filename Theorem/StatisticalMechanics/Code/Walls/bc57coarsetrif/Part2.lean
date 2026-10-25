/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc56menger.Part4
import Def.StatisticalMechanics.Code.Walls.bc57coarsetrif
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


@[simp] theorem bc57_pt_fst (k h : ℤ) : (bc57_pt k h) 0 = k := by simp [bc57_pt]

@[simp] theorem bc57_pt_snd (k h : ℤ) : (bc57_pt k h) 1 = h := by simp [bc57_pt]

theorem bc57_pt_inj {k k' h h' : ℤ} (hk : k = k') (hh : h = h') :
    bc57_pt k h = bc57_pt k' h' := by rw [hk, hh]


theorem bc57_pt_adj (k h : ℤ) :
    (hypercubicLattice 2).Adj (bc57_pt k h) (bc57_pt (k + 1) h) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc57_pt]

end StatMech.Walls
