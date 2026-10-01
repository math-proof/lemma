import sympy.sets.sets
import sympy.Basic
open Matrix


@[main]
private lemma main
  {n : ℕ}
  {A B C D : Matrix (Fin n) (Fin n) ℝ}
  {a : ℝ} :
-- imply
  A * (a • B - a • C) * D = a • (A * (B - C) * D) := by
-- proof
  rw [← smul_sub, Matrix.mul_smul, Matrix.smul_mul]


@[main]
private lemma adjugate
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ} :
-- imply
  A * A.adjugate = A.det • (1 : Matrix (Fin n) (Fin n) ℂ) := by
-- proof
  exact Matrix.mul_adjugate A


-- created on 2023-04-30
