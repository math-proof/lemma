/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.Universality.RSWTraceContact.Part3
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_closedLoop_contacts_crossingTrace_of_straddles
    {a b c d : ℤ} {u : Site 2}
    (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d)
    (hstraddle : rlc_TraceStraddlesLoop C gamma) :
    ∃ z, z ∈ rlc_pathVertices gamma ∧ z ∈ C.support := by
  obtain ⟨x, hxPath, y, hyPath, hxy⟩ := hstraddle
  let W := rlc_ambientCrossingWalk gamma
  have hxW : x ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma x).2 hxPath
  have hyW : y ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma y).2 hyPath
  let wxy : (hypercubicLattice 2).Walk x y :=
    (W.takeUntil x hxW).reverse.append (W.takeUntil y hyW)
  obtain ⟨z, hzxy, hzC⟩ :=
    rlc_closedLoop_contact_of_opposite_sides C wxy hxy
  have hzW : z ∈ W.support := by
    dsimp only [wxy] at hzxy
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hzxy
    rcases hzxy with hz | hz
    · exact W.support_takeUntil_subset_support hxW (by simpa using hz)
    · exact W.support_takeUntil_subset_support hyW hz
  exact ⟨z,
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma z).1 hzW,
    hzC⟩


theorem rlc_closedLoop_contacts_both_wiredTraces_of_straddles {n : ℤ}
    {u : Site 2} (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hright : rlc_TraceStraddlesLoop C gamma.1)
    (hleft : rlc_TraceStraddlesLoop C gamma'.1) :
    (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ C.support) ∧
      (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ C.support) := by
  exact ⟨rlc_closedLoop_contacts_crossingTrace_of_straddles C gamma.1 hright,
    rlc_closedLoop_contacts_crossingTrace_of_straddles C gamma'.1 hleft⟩


theorem rlc_closedLoop_contacts_crossingTrace {a b c d : ℤ}
    {u : Site 2} (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d)
    (hsides : rlc_OppositeLoopSides C
      (gamma.1 : Site 2) (gamma.2.1 : Site 2)) :
    ∃ z, z ∈ rlc_pathVertices gamma ∧ z ∈ C.support := by
  obtain ⟨z, hzWalk, hzC⟩ :=
    rlc_closedLoop_contact_of_opposite_sides C
      (rlc_ambientCrossingWalk gamma) hsides
  exact ⟨z, rlc_ambientCrossingWalk_support_mem_pathVertices gamma hzWalk,
    hzC⟩


theorem rlc_closedLoop_contacts_both_wiredTraces {n : ℤ}
    {u : Site 2} (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hright : rlc_OppositeLoopSides C
      (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2))
    (hleft : rlc_OppositeLoopSides C
      (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2)) :
    (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ C.support) ∧
      (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ C.support) := by
  exact ⟨rlc_closedLoop_contacts_crossingTrace C gamma.1 hright,
    rlc_closedLoop_contacts_crossingTrace C gamma'.1 hleft⟩


end Universality
end StatMech
