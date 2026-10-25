/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Def.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_stdf_radj01 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r0 rlc_stdf_r1 := by
  simp [rlc_stdf_r0, rlc_stdf_r1, hypercubicLattice_adj]

theorem rlc_stdf_radj12 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r1 rlc_stdf_r2 := by
  simp [rlc_stdf_r1, rlc_stdf_r2, hypercubicLattice_adj]

theorem rlc_stdf_radj23 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r2 rlc_stdf_r3 := by
  simp [rlc_stdf_r2, rlc_stdf_r3, hypercubicLattice_adj]

theorem rlc_stdf_radj34 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r3 rlc_stdf_r4 := by
  simp [rlc_stdf_r3, rlc_stdf_r4, hypercubicLattice_adj]

theorem rlc_stdf_radj45 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r4 rlc_stdf_r5 := by
  simp [rlc_stdf_r4, rlc_stdf_r5, hypercubicLattice_adj]

theorem rlc_stdf_radj56 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r5 rlc_stdf_r6 := by
  simp [rlc_stdf_r5, rlc_stdf_r6, hypercubicLattice_adj]

end Universality
end StatMech
