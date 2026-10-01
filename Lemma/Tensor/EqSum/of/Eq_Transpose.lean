import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {A : ℕ → ℕ → ℂ}
-- given
  (h : ∀ i j, A i j = A j i) :
-- imply
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j =
    ∑ i ∈ Finset.range n, A i i + 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, A i j := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hs : ∑ i ∈ Finset.range n, A i n = ∑ j ∈ Finset.range n, A n j := Finset.sum_congr rfl (fun i _ => h i n)
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih, hs]
    ring


-- created on 2023-05-25
