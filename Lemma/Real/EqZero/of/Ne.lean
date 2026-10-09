import Mathlib.Analysis.Calculus.Deriv.Basic
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℝ → ℝ}
  {x : Fin n → ℝ}
  {i j : Fin n}
-- given
  (hne : i ≠ j) :
-- imply
  deriv (fun t => f ((Function.update x i t) j)) (x i) = 0 := by
-- proof
  simp only [Function.update_of_ne hne.symm, deriv_const]


-- created on 2026-10-09
