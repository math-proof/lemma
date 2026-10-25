/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingConstruct
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def jwn_squareLoop : (hypercubicLattice 2).Walk ![(0:ℤ), 0] ![(0:ℤ), 0] := by
  have a1 : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have a2 : (hypercubicLattice 2).Adj ![(0:ℤ), -1] ![(1:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have a3 : (hypercubicLattice 2).Adj ![(1:ℤ), -1] ![(1:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have a4 : (hypercubicLattice 2).Adj ![(1:ℤ), 0] ![(0:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  exact .cons a1 (.cons a2 (.cons a3 (.cons a4 .nil)))


end Lattice
end StatMech
