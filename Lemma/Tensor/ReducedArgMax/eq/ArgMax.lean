import Macro.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {f : ℕ → ℝ} :
-- imply
  max⁻¹[i : Fin n] f i = max⁻¹[i : Fin n] f ↑i := by
-- proof
  rfl


-- created on 2023-11-05
