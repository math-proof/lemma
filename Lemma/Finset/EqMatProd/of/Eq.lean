import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℂ}
-- given
  (h : ∀ i < n, f i = g i) :
-- imply
  ∏ i < n, f i = ∏ i < n, g i := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  exact Finset.prod_congr rfl (fun i hi => h i (Finset.mem_range.mp hi))


-- created on 2020-10-29
