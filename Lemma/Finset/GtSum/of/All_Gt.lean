import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i < n, f i > g i) :
-- imply
  ∑ i < n, f i > ∑ i < n, g i := by
-- proof
  exact Finset.sum_lt_sum_of_nonempty ⟨0, by simpa using h₀⟩ (fun i hi => h i (by simpa using hi))


-- created on 2019-01-22
