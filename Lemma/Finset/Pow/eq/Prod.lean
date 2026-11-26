import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n t : ℕ}
  {f : ℕ → ℝ} :
-- imply
  (∏ k < n, f k) ^ t = ∏ k < n, f k ^ t := by
-- proof
  exact (Finset.prod_pow _ _ _).symm


-- created on 2020-01-31
