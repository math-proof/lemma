import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[ons_lowTempPathSign_eq_spin_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempCorrelation.lean)
-/
@[path]
private lemma ons_lowTempPathSign_eq_spin_mul_eq
  [Fintype V]
  [DecidableEq V]
  {config : ConfigSpace V}
  {u v : V}
  {path : G.Walk u v} :
-- imply
  ons_lowTempPathSign G config path = spin config u * spin config v := by
-- proof
  apply StatMech.Onsager.ons_lowTempPathSign_eq_spin_mul config path

/--
[isingWeight_eq_lowTempCutWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempCorrelation.lean)
-/
@[path]
private lemma isingWeight_eq_lowTempCutWeight_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {config : ConfigSpace V} :
-- imply
  isingWeight G beta 0 config = Real.exp (beta * G.edgeFinset.card) * Real.exp (-2 * beta) ^ (cutEdges G config).card := by
-- proof
  apply StatMech.Onsager.isingWeight_eq_lowTempCutWeight beta config

/--
[isingExpectation_twoPoint_eq_lowTempPathRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempCorrelation.lean)
-/
@[path]
private lemma isingExpectation_twoPoint_eq_lowTempPathRatio_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {u v : V}
  {path : G.Walk u v} :
-- imply
  isingExpectation G beta 0 (fun config => spin config u * spin config v) = ons_lowTempPathNumerator G beta path / ons_lowTempContourDenominator G beta := by
-- proof
  apply StatMech.Onsager.isingExpectation_twoPoint_eq_lowTempPathRatio beta path


-- created on 2026-10-23
