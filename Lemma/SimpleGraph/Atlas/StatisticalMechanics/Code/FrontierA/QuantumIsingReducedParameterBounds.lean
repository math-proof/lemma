import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingReducedParameterBounds
open StatMech StatMech.FrontierA


/--
[one_le_quantumIsingTrotterReducedParameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingReducedParameterBounds.lean)
-/
@[path]
private lemma one_le_quantumIsingTrotterReducedParameter_eq
  {n : Nat}
  {k : Real}
-- given
  (beta h : Real)
  (ht : 0 < beta / (2 * n))
  (hx : 0 < beta * h / (2 * n))
  (hx1 : beta * h / (2 * n) < 1) :
-- imply
  1 ≤ quantumIsingTrotterReducedParameter beta h n k := by
-- proof
  apply StatMech.FrontierA.one_le_quantumIsingTrotterReducedParameter beta h n k ht hx hx1


-- created on 2026-10-23
