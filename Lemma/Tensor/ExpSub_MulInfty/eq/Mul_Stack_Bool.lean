import sympy.tensor.stack
import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ* [n, n]) :
-- imply
  exp (A + ([i < n] [j < n] (Bool.toNat (p i j)) - 1 : Tensor ℝ* [n, n]) * Hyperreal.omega) = exp A * [i < n] [j < n] (Bool.toNat (p i j)) := by
-- proof
  sorry


-- created on 2025-12-05
