/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Def.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part2
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem arc_p_adj (k : ℤ) : (hypercubicLattice 2).Adj (arc_p k) (arc_p (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [arc_p]

theorem arc_p_inj : Function.Injective arc_p := by
  intro a b h
  have : (arc_p a) 0 = (arc_p b) 0 := by rw [h]
  simpa [arc_p] using this

end Percolation
end StatMech
