import Mathlib.Data.Matrix.Basic
import sympy.sets.sets
import sympy.Basic
open Matrix


@[main]
private lemma main
  {n d t : ℕ}
  {x : ℕ → ℕ → ℕ → ℝ} :
-- imply
  (Matrix.of fun i j : Fin n => x j (i + d) t) = (Matrix.of fun j i : Fin n => x j (i + d) t)ᵀ := by
-- proof
  rfl


-- created on 2026-09-27
