import Syntax.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ} :
-- imply
  sInf (f '' S) ≤ Minima S f := by
-- proof
  exact le_of_eq rfl


-- created on 2019-01-03
