import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic
open Complex


@[path]
private lemma main
  {n : ℕ}
  {x : ℝ}
  {f : ℕ → ℝ → ℂ} :
-- imply
  im (∑ k < n, f k x) = ∑ k < n, im (f k x) := by
-- proof
  simpa only [Nat.Iio_eq_range] using Complex.im_sum _ _


-- created on 2023-10-02
-- updated on 2026-11-26
