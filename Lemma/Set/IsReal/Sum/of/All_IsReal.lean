import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℂ}
-- given
  (h : ∀ i < n, x i ∈ Set.range Complex.ofReal) :
-- imply
  ∑ i < n, x i ∈ Set.range Complex.ofReal := by
-- proof
  refine ⟨∑ i < n, (x i).re, ?_⟩
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  try simp only [Nat.Iio_eq_range, ← Finset.mem_range] at *
  obtain ⟨r, hr⟩ := h i hi
  rw [← hr, Complex.ofReal_re]


-- created on 2023-05-03
