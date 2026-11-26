import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i < n, f i < 0) :
-- imply
  ∑ i < n, f i < 0 := by
-- proof
  simp only [Nat.Iio_eq_range]
  have := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr h₀.ne')
    (fun i hi => h i (by simpa using hi))
  simpa using this


-- created on 2019-01-30
