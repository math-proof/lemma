/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.Universality.RSWTraceContact.Part4
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_reflectedOpenDualCycle_contacts_both_of_straddles {n : ℤ}
    {eta : ConfigSpace (Sym2 (Site 2))} {u : Site 2}
    (c : (openSubgraph 2 eta).Walk u u)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hright : rlc_TraceStraddlesLoop
      (c.mapLe (rlc_openSubgraph_le_lattice eta)) gamma.1)
    (hleft : rlc_TraceStraddlesLoop
      (c.mapLe (rlc_openSubgraph_le_lattice eta)) gamma'.1) :
    (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ c.support) ∧
      (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ c.support) := by
  let C : (hypercubicLattice 2).Walk u u :=
    c.mapLe (rlc_openSubgraph_le_lattice eta)
  obtain ⟨⟨x, hxPath, hxC⟩, ⟨y, hyPath, hyC⟩⟩ :=
    rlc_closedLoop_contacts_both_wiredTraces_of_straddles
      C gamma gamma' hright hleft
  exact ⟨⟨x, hxPath, by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hxC⟩,
    ⟨y, hyPath, by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hyC⟩⟩


theorem rlc_reflectedOpenDualCycle_contacts_both_wiredTraces {n : ℤ}
    {eta : ConfigSpace (Sym2 (Site 2))} {u : Site 2}
    (c : (openSubgraph 2 eta).Walk u u)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hright : rlc_OppositeLoopSides
      (c.mapLe (rlc_openSubgraph_le_lattice eta))
      (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2))
    (hleft : rlc_OppositeLoopSides
      (c.mapLe (rlc_openSubgraph_le_lattice eta))
      (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2)) :
    (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ c.support) ∧
      (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ c.support) := by
  let C : (hypercubicLattice 2).Walk u u :=
    c.mapLe (rlc_openSubgraph_le_lattice eta)
  obtain ⟨⟨x, hxPath, hxC⟩, ⟨y, hyPath, hyC⟩⟩ :=
    rlc_closedLoop_contacts_both_wiredTraces C gamma gamma' hright hleft
  exact ⟨⟨x, hxPath, by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hxC⟩,
    ⟨y, hyPath, by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hyC⟩⟩

end Universality
end StatMech
