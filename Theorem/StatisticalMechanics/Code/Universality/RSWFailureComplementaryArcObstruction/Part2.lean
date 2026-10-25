/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Def.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_stdf_ladj01 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l0 rlc_stdf_l1 := by
  simp [rlc_stdf_l0, rlc_stdf_l1, hypercubicLattice_adj]

theorem rlc_stdf_ladj12 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l1 rlc_stdf_l2 := by
  simp [rlc_stdf_l1, rlc_stdf_l2, hypercubicLattice_adj]

theorem rlc_stdf_ladj23 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l2 rlc_stdf_l3 := by
  simp [rlc_stdf_l2, rlc_stdf_l3, hypercubicLattice_adj]

theorem rlc_stdf_ladj34 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l3 rlc_stdf_l4 := by
  simp [rlc_stdf_l3, rlc_stdf_l4, hypercubicLattice_adj]

theorem rlc_stdf_ladj45 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l4 rlc_stdf_l5 := by
  simp [rlc_stdf_l4, rlc_stdf_l5, hypercubicLattice_adj]

theorem rlc_stdf_ladj56 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l5 rlc_stdf_l6 := by
  simp [rlc_stdf_l5, rlc_stdf_l6, hypercubicLattice_adj]

end Universality
end StatMech
