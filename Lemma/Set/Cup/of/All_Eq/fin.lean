import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → Set α}
-- given
  (h : ∀ i < n, f i = g i) :
-- imply
  ⋃ i < n, f i = ⋃ i < n, g i := by
-- proof
  exact Set.iUnion₂_congr h


-- created on 2018-09-28
