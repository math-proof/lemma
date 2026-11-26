import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a : ℤ}
  (f g : ℤ → ℕ)
  (x : ℤ → ℕ → ℕ → ℝ) :
-- imply
  ∏ i ∈ ({a} : Finset ℤ), ∏ j < (f i), ∏ k < (g i), x i j k
    = ∏ j < (f a), ∏ k < (g a), x a j k := by
-- proof
  simp


-- created on 2020-03-05
-- updated on 2026-10-26
