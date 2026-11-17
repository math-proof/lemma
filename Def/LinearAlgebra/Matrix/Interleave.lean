module

public import Def.Analysis.SpecialFunctions.TensorFunctions
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

/--
Even/odd gather on `Fin (d + d)`:
row `k < d` is `δ(j, 2k)`, and row `k ≥ d` is `δ(j, 2(k - d) + 1)`.
-/
def Matrix.interleave (d : ℕ) : Matrix (Fin (d + d)) (Fin (d + d)) ℝ :=
  Matrix.of fun k j =>
    if (k : ℕ) < d then
      (KroneckerDelta (j : ℕ) (2 * (k : ℕ)) : ℝ)
    else
      (KroneckerDelta (j : ℕ) (2 * ((k : ℕ) - d) + 1) : ℝ)
