import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n i : ℕ}
  {a : ℕ → Fin n → ℝ} :
-- imply
  (fun k : Fin 4 => a (i + k)) =
    Matrix.vecCons (a i) (Matrix.vecCons (a (i + 1)) (Matrix.vecCons (a (i + 2)) (Matrix.vecCons (a (i + 3)) Matrix.vecEmpty))) := by
-- proof
  funext k
  fin_cases k <;> rfl


-- created on 2026-09-27
