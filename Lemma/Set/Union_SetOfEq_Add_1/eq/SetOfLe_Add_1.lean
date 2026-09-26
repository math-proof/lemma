import Mathlib.Data.Set.Basic
import sympy.Basic


@[main]
private lemma main
  {Ω : Type*}
-- given
  (D : Ω → ℕ)
  (m : ℕ) :
-- imply
  {ω | D ω ≤ m} ∪ {ω | D ω = m + 1} = {ω | D ω ≤ m + 1} := by
-- proof
  ext
  simp
  omega


-- created on 2026-09-26
