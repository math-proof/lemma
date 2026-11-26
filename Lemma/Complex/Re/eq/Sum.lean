import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic
open Complex


@[path]
private lemma main
  {n : ℕ}
  {x : ℝ}
  {f : ℕ → ℝ → ℂ} :
-- imply
  re (∑ k < n, f k x) = ∑ k < n, re (f k x) := by
-- proof
  simpa only [Nat.Iio_eq_range] using Complex.re_sum _ _


-- created on 2023-10-02
-- updated on 2026-11-26
