import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversalCounterexample.Part2
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalGateCounterColoring_leftSourcePattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversalCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounterColoring_leftSourcePattern_eq :
-- imply
  LeftSourcePattern canonicalGateCounterEnds canonicalGateCounterSupport {0, 1} {1, 2} canonicalGateCounterColoring := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounterColoring_leftSourcePattern

/--
[canonicalGateCounterColoring_rows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversalCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounterColoring_rows_eq :
-- imply
  rowClass canonicalGateCounterSupport canonicalGateCounterColoring 0 = canonicalGateCounterK ∧ rowClass canonicalGateCounterSupport canonicalGateCounterColoring 1 = canonicalGateCounterL := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounterColoring_rows

/--
[canonicalGateCounterColoring_middleSwap_rows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversalCounterexample.lean)
-/
@[path]
private lemma canonicalGateCounterColoring_middleSwap_rows_eq :
-- imply
  rowClass canonicalGateCounterSupport (middleSwap canonicalGateCounterSupport canonicalGateCounterColoring) 0 = canonicalGateCounterA ∧ rowClass canonicalGateCounterSupport (middleSwap canonicalGateCounterSupport canonicalGateCounterColoring) 1 = canonicalGateCounterB := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalGateCounterColoring_middleSwap_rows

/--
[middleSwap_rowsDisconnect_implication_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversalCounterexample.lean)
-/
@[path]
private lemma middleSwap_rowsDisconnect_implication_false_eq :
-- imply
  RowsDisconnect canonicalGateCounterEnds canonicalGateCounterSupport canonicalGateCounterColoring 1 3 ∧ ¬ RowsDisconnect canonicalGateCounterEnds canonicalGateCounterSupport (middleSwap canonicalGateCounterSupport canonicalGateCounterColoring) 1 3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.middleSwap_rowsDisconnect_implication_false

/--
[sourceMaskFiber_gate_implication_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversalCounterexample.lean)
-/
@[path]
private lemma sourceMaskFiber_gate_implication_false_eq :
-- imply
  ∃ c : leftSourceMaskFiber canonicalGateCounterEnds canonicalGateCounterSupport 0 1 2 3 canonicalGateCounterMaskProfile, RowsDisconnect canonicalGateCounterEnds canonicalGateCounterSupport c.1 1 3 ∧ ¬ RowsDisconnect canonicalGateCounterEnds canonicalGateCounterSupport (middleSwap canonicalGateCounterSupport c.1) 1 3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sourceMaskFiber_gate_implication_false


-- created on 2026-10-23
