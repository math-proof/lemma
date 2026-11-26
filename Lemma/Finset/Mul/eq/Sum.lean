import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma as_multiple_limits
  {n m : ℕ}
  {f g : ℕ → ℤ} :
-- imply
  (∑ i < m, f i) * ∑ i < n, g i = ∑ i < m, ∑ j < n, f i * g j := by
-- proof
  exact Finset.sum_mul_sum _ _ _ _


-- created on 2020-02-02
