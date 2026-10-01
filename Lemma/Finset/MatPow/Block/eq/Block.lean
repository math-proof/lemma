import Mathlib.Data.Matrix.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {X : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℝ} :
-- imply
  (Matrix.of fun p q : Fin 3 × Fin n => X p.1 q.1 p.2 q.2) ^ 2 = Matrix.of fun p q : Fin 3 × Fin n => (∑ k, X p.1 k * X k q.1) p.2 q.2 := by
-- proof
  ext p q
  rw [sq, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply]


-- created on 2023-09-16
