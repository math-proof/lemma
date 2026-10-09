import sympy.Basic
open Matrix


@[path]
private lemma main
  {n m k : ℕ}
  {h : ℕ → Fin m → ℝ} :
-- imply
  (Matrix.of fun (i : Fin m) (j : Fin n) => h (j + k) i) = (Matrix.of fun (j : Fin n) (i : Fin m) => h (j + k) i)ᵀ :=
-- proof
  rfl


-- created on 2022-01-11
