import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {A B C D : Matrix (Fin n) (Fin n) ℝ}
  {a : ℝ} :
-- imply
  A * (a • B - a • C) * D = a • (A * (B - C) * D) := by
-- proof
  rw [← smul_sub, Matrix.mul_smul, Matrix.smul_mul]


-- created on 2020-02-10
