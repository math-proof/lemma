import Syntax.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {f : ℕ → ℝ} :
-- imply
  min⁻¹[i : Fin n] f i = min⁻¹[i : Fin n] f ↑i :=
-- proof
  rfl


-- created on 2023-11-05
