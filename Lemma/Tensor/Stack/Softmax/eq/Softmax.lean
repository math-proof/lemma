import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[main]
private lemma main
  {x : Fin m → Fin n → ℝ} :
-- imply
  (fun i => fun j => Real.exp (x i j) / ∑ k, Real.exp (x i k)) = fun i j => Real.exp (x i j) / ∑ k, Real.exp (x i k) :=
-- proof
  rfl


-- created on 2026-09-27
