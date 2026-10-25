import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWTraceContact.Part4
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_closedLoop_contact_of_opposite_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean)
-/
@[path]
private lemma rlc_closedLoop_contact_of_opposite_sides_eq
  {a x y : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hxy : rlc_OppositeLoopSides C x y) :
-- imply
  ∃ z ∈ w.support, z ∈ C.support := by
-- proof
  apply StatMech.Universality.rlc_closedLoop_contact_of_opposite_sides C w hxy

/--
[rlc_ambientCrossingWalk_support_mem_pathVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean)
-/
@[path]
private lemma rlc_ambientCrossingWalk_support_mem_pathVertices_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d}
  {z : Site 2}
-- given
  (hz : z ∈ (rlc_ambientCrossingWalk gamma).support) :
-- imply
  z ∈ rlc_pathVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_ambientCrossingWalk_support_mem_pathVertices gamma hz

/--
[rlc_mem_ambientCrossingWalk_support_iff_pathVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean)
-/
@[path]
private lemma rlc_mem_ambientCrossingWalk_support_iff_pathVertices_eq
  {a b c d : ℤ}
  {gamma : RlcCrossingPath a b c d}
  {z : Site 2} :
-- imply
  z ∈ (rlc_ambientCrossingWalk gamma).support ↔ z ∈ rlc_pathVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma z

/--
[rlc_closedLoop_contacts_crossingTrace_of_straddles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean)
-/
@[path]
private lemma rlc_closedLoop_contacts_crossingTrace_of_straddles_eq
  {a b c d : ℤ}
  {u : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
  {gamma : RlcCrossingPath a b c d}
-- given
  (hstraddle : rlc_TraceStraddlesLoop C gamma) :
-- imply
  ∃ z, z ∈ rlc_pathVertices gamma ∧ z ∈ C.support := by
-- proof
  apply StatMech.Universality.rlc_closedLoop_contacts_crossingTrace_of_straddles C gamma hstraddle

/--
[rlc_closedLoop_contacts_both_wiredTraces_of_straddles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean)
-/
@[path]
private lemma rlc_closedLoop_contacts_both_wiredTraces_of_straddles_eq
  {n : ℤ}
  {u : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hright : rlc_TraceStraddlesLoop C gamma.1)
  (hleft : rlc_TraceStraddlesLoop C gamma'.1) :
-- imply
  (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ C.support) ∧ (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ C.support) := by
-- proof
  apply StatMech.Universality.rlc_closedLoop_contacts_both_wiredTraces_of_straddles C gamma gamma' hright hleft

/--
[rlc_closedLoop_contacts_crossingTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean)
-/
@[path]
private lemma rlc_closedLoop_contacts_crossingTrace_eq
  {a b c d : ℤ}
  {u : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
  {gamma : RlcCrossingPath a b c d}
-- given
  (hsides : rlc_OppositeLoopSides C (gamma.1 : Site 2) (gamma.2.1 : Site 2)) :
-- imply
  ∃ z, z ∈ rlc_pathVertices gamma ∧ z ∈ C.support := by
-- proof
  apply StatMech.Universality.rlc_closedLoop_contacts_crossingTrace C gamma hsides

/--
[rlc_closedLoop_contacts_both_wiredTraces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean)
-/
@[path]
private lemma rlc_closedLoop_contacts_both_wiredTraces_eq
  {n : ℤ}
  {u : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hright : rlc_OppositeLoopSides C (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2))
  (hleft : rlc_OppositeLoopSides C (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2)) :
-- imply
  (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ C.support) ∧ (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ C.support) := by
-- proof
  apply StatMech.Universality.rlc_closedLoop_contacts_both_wiredTraces C gamma gamma' hright hleft

/--
[rlc_reflectedOpenDualCycle_contacts_both_of_straddles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean)
-/
@[path]
private lemma rlc_reflectedOpenDualCycle_contacts_both_of_straddles_eq
  {n : ℤ}
  {eta : ConfigSpace (Sym2 (Site 2))}
  {u : Site 2}
  {c : (openSubgraph 2 eta).Walk u u}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hright : rlc_TraceStraddlesLoop (c.mapLe (rlc_openSubgraph_le_lattice eta)) gamma.1)
  (hleft : rlc_TraceStraddlesLoop (c.mapLe (rlc_openSubgraph_le_lattice eta)) gamma'.1) :
-- imply
  (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ c.support) ∧ (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_reflectedOpenDualCycle_contacts_both_of_straddles c gamma gamma' hright hleft

/--
[rlc_reflectedOpenDualCycle_contacts_both_wiredTraces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceContact.lean)
-/
@[path]
private lemma rlc_reflectedOpenDualCycle_contacts_both_wiredTraces_eq
  {n : ℤ}
  {eta : ConfigSpace (Sym2 (Site 2))}
  {u : Site 2}
  {c : (openSubgraph 2 eta).Walk u u}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hright : rlc_OppositeLoopSides (c.mapLe (rlc_openSubgraph_le_lattice eta)) (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2))
  (hleft : rlc_OppositeLoopSides (c.mapLe (rlc_openSubgraph_le_lattice eta)) (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2)) :
-- imply
  (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ c.support) ∧ (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_reflectedOpenDualCycle_contacts_both_wiredTraces c gamma gamma' hright hleft


-- created on 2026-10-23
