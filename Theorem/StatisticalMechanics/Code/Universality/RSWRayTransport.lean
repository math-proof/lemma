/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_oppositeLoopSides_iff_leftRegion_xor
    {a : Site 2} (C : (hypercubicLattice 2).Walk a a) (x y : Site 2) :
    rlc_OppositeLoopSides C x y ↔
      (x ∈ jec_leftRegion C ∧ y ∉ jec_leftRegion C) ∨
        (x ∉ jec_leftRegion C ∧ y ∈ jec_leftRegion C) := by
  simp only [rlc_OppositeLoopSides, jec_mem_leftRegion]
  tauto


theorem rlc_not_oppositeLoopSides_of_both_mem_leftRegion
    {a : Site 2} (C : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (hx : x ∈ jec_leftRegion C) (hy : y ∈ jec_leftRegion C) :
    ¬ rlc_OppositeLoopSides C x y := by
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor]
  tauto


theorem rlc_not_oppositeLoopSides_of_both_not_mem_leftRegion
    {a : Site 2} (C : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (hx : x ∉ jec_leftRegion C) (hy : y ∉ jec_leftRegion C) :
    ¬ rlc_OppositeLoopSides C x y := by
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor]
  tauto


end Universality
end StatMech
