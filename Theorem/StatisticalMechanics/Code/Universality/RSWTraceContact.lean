/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.Universality.RSWTraceContact
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_closedLoop_contact_of_opposite_sides {a x y : Site 2}
    (C : (hypercubicLattice 2).Walk a a)
    (w : (hypercubicLattice 2).Walk x y)
    (hxy : rlc_OppositeLoopSides C x y) :
    ∃ z ∈ w.support, z ∈ C.support := by
  rcases hxy with hxy | hxy
  · obtain ⟨z, hz, hzC⟩ :=
      ccs_closedLoop_separatingSide_forces_cross C
        ({y} : Set (Site 2)) ({x} : Set (Site 2))
        (by simpa using hxy.2) (by simpa using hxy.1)
        (by simp) (by simp) w.reverse
    exact ⟨z, by simpa [SimpleGraph.Walk.support_reverse] using hz, hzC⟩
  · exact ccs_closedLoop_separatingSide_forces_cross C
      ({x} : Set (Site 2)) ({y} : Set (Site 2))
      (by simpa using hxy.1) (by simpa using hxy.2)
      (by simp) (by simp) w


end Universality
end StatMech
