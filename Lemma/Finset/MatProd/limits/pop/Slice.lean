import Mathlib.Data.Matrix.Mul
import sympy.Basic


@[path]
private lemma main
  {m : ℕ}
  {f : ℕ → Matrix (Fin m) (Fin m) ℝ}
  {i n : ℕ}
-- given
  (h₀ : i ≤ n) :
-- imply
  ((List.range (n + 1 - i)).map fun k => f (i + k)).prod
    = ((List.range (n - i)).map fun k => f (i + k)).prod * f n := by
-- proof
  have hlen : n + 1 - i = (n - i) + 1 := by omega
  rw [hlen, List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
  simp [show i + (n - i) = n by omega]


-- created on 2023-11-18
-- updated on 2026-10-17
