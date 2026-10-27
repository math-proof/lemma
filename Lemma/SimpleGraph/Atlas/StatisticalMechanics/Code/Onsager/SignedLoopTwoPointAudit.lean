import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopTwoPointAudit
open Finset StatMech StatMech.Onsager


/--
[ons_finiteTwoPoint_highTemp_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopTwoPointAudit.lean)
-/
@[path]
private lemma ons_finiteTwoPoint_highTemp_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  isingExpectation G beta 0 (fun s => spin s u * spin s v) = ons_sourceX G {u, v} (Real.tanh beta) / ons_X G (Real.tanh beta) := by
-- proof
  apply StatMech.Onsager.ons_finiteTwoPoint_highTemp_ratio beta huv

/--
[ons_finiteTwoPoint_critical_source_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopTwoPointAudit.lean)
-/
@[path]
private lemma ons_finiteTwoPoint_critical_source_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  isingExpectation G ons_betaC 0 (fun s => spin s u * spin s v) = ons_sourceX G {u, v} ons_signedLoopCriticalWeight / ons_X G ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.ons_finiteTwoPoint_critical_source_ratio huv


-- created on 2026-10-23
