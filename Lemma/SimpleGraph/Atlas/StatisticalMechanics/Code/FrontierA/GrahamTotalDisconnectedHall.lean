import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTotalDisconnectedHall.Part2
open Finset Classical StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[rowsDisconnect_of_total_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTotalDisconnectedHall.lean)
-/
@[path]
private lemma rowsDisconnect_of_total_disconnected_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {k zero : W}
  {c : ↑m → Fin 4}
-- given
  (hdisc : ¬ connK ends m k zero) :
-- imply
  RowsDisconnect ends m c k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowsDisconnect_of_total_disconnected ends m k zero hdisc c

/--
[rowDataRepairHall_of_total_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTotalDisconnectedHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_total_disconnected_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
-- given
  (hdisc : ¬ connK ends m k zero) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_total_disconnected ends m j k l zero hdisc


-- created on 2026-10-23
