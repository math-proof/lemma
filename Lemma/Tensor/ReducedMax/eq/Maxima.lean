import Syntax.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ} :
-- imply
  sSup (f '' S) = Maxima S f := by
-- proof
  rfl


-- created on 2018-12-31
