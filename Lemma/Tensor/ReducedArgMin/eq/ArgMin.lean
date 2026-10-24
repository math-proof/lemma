import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {f : ℕ → ℝ} :
-- imply
  min⁻¹[i : Fin n] f i = min⁻¹[i : Fin n] f ↑i :=
-- proof
  rfl


-- created on 2023-11-05
