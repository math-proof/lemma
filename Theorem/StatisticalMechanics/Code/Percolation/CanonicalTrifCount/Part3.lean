/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Def.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part3
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


namespace CtcWitness

theorem px_inj : Function.Injective px := by
  intro a b h
  have h0 : (px a) 0 = (px b) 0 := by rw [h]
  simpa [px] using h0

theorem py_inj : Function.Injective py := by
  intro a b h
  have h1 : (py a) 1 = (py b) 1 := by rw [h]
  simpa [py] using h1

theorem px_adj (k : ℤ) : (hypercubicLattice 2).Adj (px k) (px (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [px]

theorem py_adj (k : ℤ) : (hypercubicLattice 2).Adj (py k) (py (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [py]

end CtcWitness
end Percolation
end StatMech
