import sympy.Basic
import Mathlib.Data.Fin.VecNotation


@[main]
private lemma main
  {i : ℕ}
  {a : ℕ → α} :
-- imply
  (fun j : Fin 4 => a (i + j)) =
    Matrix.vecCons (a i) (Matrix.vecCons (a (i + 1)) (Matrix.vecCons (a (i + 2)) (Matrix.vecCons (a (i + 3)) Matrix.vecEmpty))) := by
-- proof
  funext j
  fin_cases j <;> rfl


-- created on 2020-03-12
