import Mathlib.Data.Matrix.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  (Matrix.of fun i j : Fin n => if i = j then (1 : ℝ) else 0) = 1 := by
-- proof
  ext i j
  simp [Matrix.one_apply]


-- created on 2023-03-18
