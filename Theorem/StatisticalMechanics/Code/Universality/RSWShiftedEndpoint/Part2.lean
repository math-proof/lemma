/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
import Def.StatisticalMechanics.Code.Universality.RSWShiftedEndpoint
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_right_end_shiftedPreimage_not_mem_rightPath {n : ℤ}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n) :
    rlc_shiftedEndpointPreimage (gamma.1.2.1 : Site 2) ∉
      rlc_pathVertices gamma.1 := by
  intro h
  have hrect := rlc_pathVertex_mem_rect gamma.1 h
  have hend := gamma.1.2.1.2
  rw [mem_rect] at hrect
  rw [mem_rightSide] at hend
  have hx : (gamma.1.2.1 : Site 2) 0 = 2 * n := hend.2
  have hxLower := hrect.1
  simp only [rlc_shiftedEndpointPreimage_zero] at hxLower
  omega


theorem rlc_left_start_shiftedPreimage_not_mem_leftPath {n : ℤ}
    (hn : 0 < n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_shiftedEndpointPreimage (gamma'.1.1 : Site 2) ∉
      rlc_pathVertices gamma'.1 := by
  intro h
  have hrect := rlc_pathVertex_mem_rect gamma'.1 h
  have hstart := gamma'.1.1.2
  rw [mem_rect] at hrect
  rw [mem_leftSide] at hstart
  have hx : (gamma'.1.1 : Site 2) 0 = -2 * n := hstart.2
  have hxUpper := hrect.2.1
  simp only [rlc_shiftedEndpointPreimage_zero] at hxUpper
  omega


end Universality
end StatMech
