import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ} :
-- imply
  A * A.adjugate = A.det • (1 : Matrix (Fin n) (Fin n) ℂ) :=
-- proof
  Matrix.mul_adjugate A


-- created on 2026-10-09
