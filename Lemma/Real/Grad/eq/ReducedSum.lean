import Mathlib.Analysis.Calculus.FDeriv.Add
import sympy.Basic


@[path]
private lemma main
  {n d : ℕ}
  {f : (Fin n → ℝ) → Fin d → ℝ}
  {x : Fin n → ℝ}
-- given
  (h : ∀ j : Fin d, DifferentiableAt ℝ (fun x' => f x' j) x) :
-- imply
  fderiv ℝ (fun x' => ∑ j : Fin d, f x' j) x = ∑ j : Fin d, fderiv ℝ (fun x' => f x' j) x := by
-- proof
  apply fderiv_fun_sum
  intro j _
  apply h j


-- created on 2026-10-07
