import Initialize.Tactic.Attr.Basic
import Syntax.Order.ExprWithLimits
import Mathlib.Analysis.SpecialFunctions.Exp


@[path]
private lemma main
  [NeZero n]
  {x : Fin n → ℝ} :
-- imply
  «min⁻¹» Set.univ (fun j => Real.exp (x j)) = «min⁻¹» Set.univ x := by
-- proof
  unfold «min⁻¹»
  congr 1
  funext k
  simp only [Real.exp_le_exp]


-- created on 2021-12-20
-- updated on 2026-11-13
