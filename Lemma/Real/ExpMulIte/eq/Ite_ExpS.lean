import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[main]
private lemma main
  {A : Set ℝ} [DecidablePred (· ∈ A)]
  {x : ℝ}
  {g h : ℝ → ℝ} :
-- imply
  Real.exp (if x ∈ A then g x else h x) = if x ∈ A then Real.exp (g x) else Real.exp (h x) :=
-- proof
  apply_ite Real.exp _ _ _


-- created on 2026-09-27
