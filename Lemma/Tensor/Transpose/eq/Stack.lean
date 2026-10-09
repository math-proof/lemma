import sympy.Basic
open Matrix


@[path]
private lemma main
  {n m j : ℕ}
  {d : Fin m → ℕ}
  {h : ℕ → ℕ → Fin n → ℝ} :
-- imply
  (Matrix.of fun (i : Fin m) (a : Fin n) => h j (d i) a)ᵀ = Matrix.of fun (a : Fin n) (i : Fin m) => h j (d i) a :=
-- proof
  rfl


-- created on 2022-01-11
