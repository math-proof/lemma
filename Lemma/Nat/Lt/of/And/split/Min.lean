import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma given
  [LinearOrder α]
  {x a b : α}
-- given
  (h₀ : x < a)
  (h₁ : x < b) :
-- imply
  x < min a b := by
-- proof
  exact lt_min h₀ h₁


-- created on 2019-12-16
