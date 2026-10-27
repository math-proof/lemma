import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [CommMonoid α]
  {m d : ℕ}
  {M : ℕ → α} :
-- imply
  ∏ n ∈ Finset.range m, M n = ∏ n ∈ Finset.Ico d (m + d), M (n - d) := by
-- proof
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  refine Finset.prod_congr rfl ?_
  intro n _
  congr 1
  omega


-- created on 2020-08-30
-- updated on 2026-10-26
