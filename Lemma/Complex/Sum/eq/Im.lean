import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic
open Complex


@[path]
private lemma main
  {n : ℕ}
  {z : ℕ → ℂ} :
-- imply
  ∑ k < n, im (z k) = im (∑ k < n, z k) := by
-- proof
  simpa only [Nat.Iio_eq_range] using (Complex.im_sum _ _).symm


-- created on 2023-06-03
-- updated on 2026-11-26
