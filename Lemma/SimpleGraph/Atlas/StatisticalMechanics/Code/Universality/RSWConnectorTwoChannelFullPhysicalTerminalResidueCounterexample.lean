import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalTerminalResidueCounterexample
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_retainedChoiceAudit_topWall_literalTerminalSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalTerminalResidueCounterexample.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_topWall_literalTerminalSquare_eq :
-- imply
  let f : Site 2 := ![-3, 1] let g : Site 2 := ![-3, 2] let p : Site 2 := ![-3, 2] let q : Site 2 := ![-2, 2] (hypercubicLattice 2).Adj f g ∧ RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (rlc_dualReflect f) ∧ sharedPrimalEdge f g = s(p, q) ∧ p 1 = 2 ∧ p = g ∧ q ∈ rlc_pathVertices rlc_retainedChoiceAuditLeft.1 ∧ phb_doubleDualShift q = f := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_topWall_literalTerminalSquare

/--
[rlc_retainedChoiceAudit_reflectedRight_literalTerminalSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalTerminalResidueCounterexample.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_reflectedRight_literalTerminalSquare_eq :
-- imply
  let f : Site 2 := ![-2, -2] let g : Site 2 := ![-2, -1] let p : Site 2 := ![-2, -1] let q : Site 2 := ![-1, -1] (hypercubicLattice 2).Adj f g ∧ RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (rlc_dualReflect f) ∧ sharedPrimalEdge f g = s(p, q) ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft p ∧ p = g ∧ q ∈ rlc_pathVertices rlc_retainedChoiceAuditLeft.1 ∧ phb_doubleDualShift q = f := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_reflectedRight_literalTerminalSquare

/--
[exists_bookFaithful_topWall_literalTerminalSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalTerminalResidueCounterexample.lean)
-/
@[path]
private lemma exists_bookFaithful_topWall_literalTerminalSquare_eq :
-- imply
  ∃ n : Int, ∃ gamma : RlcRightDiagonalPath n, ∃ gamma' : RlcLeftDiagonalPath n, RlcBookFaithfulTracePair gamma gamma' ∧ ∃ f g p q : Site 2, (hypercubicLattice 2).Adj f g ∧ RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f) ∧ sharedPrimalEdge f g = s(p, q) ∧ p 1 = n ∧ p = g ∧ q ∈ rlc_pathVertices gamma'.1 ∧ phb_doubleDualShift q = f := by
-- proof
  apply StatMech.Universality.exists_bookFaithful_topWall_literalTerminalSquare

/--
[exists_bookFaithful_reflectedRight_literalTerminalSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalTerminalResidueCounterexample.lean)
-/
@[path]
private lemma exists_bookFaithful_reflectedRight_literalTerminalSquare_eq :
-- imply
  ∃ n : Int, ∃ gamma : RlcRightDiagonalPath n, ∃ gamma' : RlcLeftDiagonalPath n, RlcBookFaithfulTracePair gamma gamma' ∧ ∃ f g p q : Site 2, (hypercubicLattice 2).Adj f g ∧ RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f) ∧ sharedPrimalEdge f g = s(p, q) ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ p = g ∧ q ∈ rlc_pathVertices gamma'.1 ∧ phb_doubleDualShift q = f := by
-- proof
  apply StatMech.Universality.exists_bookFaithful_reflectedRight_literalTerminalSquare


-- created on 2026-10-23
