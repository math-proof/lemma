import sympy.Basic
import sympy.integrals.integrals
open MeasureTheory


@[main, comm]
private lemma main
  {n : ℕ}
  {f : Fin n → ℝ → ℝ}
  {a b : ℝ}
-- given
  (h : ∀ k : Fin n, f k ∈ ℒ¹ a b) :
-- imply
  ∫ x : ℝ in a..b, ∑ k : Fin n, f k x = ∑ k : Fin n, ∫ x : ℝ in a..b, f k x :=
-- proof
  intervalIntegral.integral_finsetSum fun k _ => h k


-- created on 2026-09-26
