import sympy.core.relational
import sympy.tensor.stack
import sympy.tensor.functions



@[main]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ* [n, n]) :
-- imply
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  exp (A + (mask - 1) * Hyperreal.omega) = exp A * mask := by
-- proof
  intro mask
  denote h_A : A' = A + (mask - 1) * Hyperreal.omega
  sorry


-- created on 2025-12-05
-- updated on 2025-12-06
