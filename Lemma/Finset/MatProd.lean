import Mathlib.Data.Matrix.Mul
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma limits.subst.offset
  {m k : ℕ}
  {d : ℤ}
  {f : ℤ → Matrix (Fin k) (Fin k) ℝ} :
-- imply
  ((List.range m).map fun n => f n).prod = ((List.range m).map fun n => f ((n + d : ℤ) - d)).prod := by
-- proof
  simp only [add_sub_cancel_right]


-- created on 2026-09-27
