/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Walls.jc6_ivt
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


noncomputable def jc6_vArc : (hypercubicLattice 2).Walk (![0, 0] : Site 2) (![0, 2] : Site 2) :=
  (SimpleGraph.Walk.nil.cons (by
      rw [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp)
    : (hypercubicLattice 2).Walk (![0, 1] : Site 2) (![0, 2] : Site 2)).cons
    (by rw [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp)


end Walls
end StatMech
