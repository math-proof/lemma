import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n i : ℕ} :
-- imply
  ∑ k ∈ Finset.range n, (i + k).choose i = (n + i).choose (i + 1) := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show n + 1 + i = (n + i) + 1 by omega, Nat.choose_succ_succ, add_comm i n, add_comm]


-- created on 2023-06-03
