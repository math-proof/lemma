import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[path]
private lemma main
  {n d : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {V z : Matrix (Fin n) (Fin d) ℝ}
  {i : Fin n}
-- given
  (h : z = (Matrix.of fun i j => Real.exp (A i j) / ∑ k, Real.exp (A i k)) * V) :
-- imply
  z i = Matrix.vecMul (fun j => Real.exp (A i j) / ∑ k, Real.exp (A i k)) V := by
-- proof
  subst h
  rfl


-- created on 2021-08-25
