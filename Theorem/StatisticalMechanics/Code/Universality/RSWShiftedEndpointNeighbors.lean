/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpointNeighbors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWShiftedEndpoint.Part3
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_right_start_shiftedPreimage_not_mem_of_bottom {n : ℤ}
    (gamma : RlcRightDiagonalPath n)
    (hbottom : (gamma.1.1 : Site 2) 1 = -n) :
    rlc_shiftedEndpointPreimage (gamma.1.1 : Site 2) ∉
      rlc_pathVertices gamma.1 := by
  intro hmem
  have hrect := rlc_pathVertex_mem_rect gamma.1 hmem
  rw [mem_rect] at hrect
  simp only [rlc_shiftedEndpointPreimage_one] at hrect
  omega


theorem rlc_not_shiftedEndpointTraceNeighbors_of_right_start_bottom {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hbottom : (gamma.1.1 : Site 2) 1 = -n) :
    ¬ RlcShiftedEndpointTraceNeighbors gamma gamma' := by
  intro h
  exact (rlc_right_start_shiftedPreimage_not_mem_of_bottom gamma hbottom)
    h.right_start_mem_right

end Universality
end StatMech
