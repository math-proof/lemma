import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolReduction.Part2
open StatMech StatMech.FrontierA


/--
[cosh_div_sinh_neg_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolReduction.lean)
-/
@[path]
private lemma cosh_div_sinh_neg_log_eq
  {x : Real}
-- given
  (hx : 0 < x)
  (hx1 : x < 1) :
-- imply
  Real.cosh (-Real.log x) / Real.sinh (-Real.log x) = (1 + x ^ 2) / (1 - x ^ 2) := by
-- proof
  apply StatMech.FrontierA.cosh_div_sinh_neg_log hx hx1

/--
[one_div_sinh_neg_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolReduction.lean)
-/
@[path]
private lemma one_div_sinh_neg_log_eq
  {x : Real}
-- given
  (hx : 0 < x)
  (hx1 : x < 1) :
-- imply
  1 / Real.sinh (-Real.log x) = 2 * x / (1 - x ^ 2) := by
-- proof
  apply StatMech.FrontierA.one_div_sinh_neg_log hx hx1

/--
[triangularIsingTrotterSymbol_reduced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolReduction.lean)
-/
@[path]
private lemma triangularIsingTrotterSymbol_reduced_eq
  {n : Nat}
  {k q : Real}
-- given
  (beta h : Real)
  (hx : 0 < beta * h / (2 * n))
  (hx1 : beta * h / (2 * n) < 1) :
-- imply
  triangularIsingSymbol (beta / (4 * n)) (quantumIsingVerticalCoupling beta h n) 0 (k + Real.pi) q / Real.sinh (2 * quantumIsingVerticalCoupling beta h n) = quantumIsingTrotterReducedParameter beta h n k - Real.cos q := by
-- proof
  apply StatMech.FrontierA.triangularIsingTrotterSymbol_reduced beta h n k q hx hx1


-- created on 2026-10-23
