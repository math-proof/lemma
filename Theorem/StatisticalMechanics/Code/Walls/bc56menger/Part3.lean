/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc55route
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Def.StatisticalMechanics.Code.Walls.bc56menger.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc56_lp_inj : Function.Injective bc56_lp := by
  intro a b h
  have h0 : (bc56_lp a) 0 = (bc56_lp b) 0 := by rw [h]
  simpa [bc56_lp] using h0


@[simp] theorem bc56_lp_snd (k : ℤ) : (bc56_lp k) 1 = 2 := by simp [bc56_lp]

theorem bc56_lp_adj (k : ℤ) : (hypercubicLattice 2).Adj (bc56_lp k) (bc56_lp (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc56_lp]

end StatMech.Walls
