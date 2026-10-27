import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [CommSemiring α]
  {x y : α}
-- given
  (n : ℕ) :
-- imply
  (x + y) ^ n = ∑ k ∈ range (n + 1), x ^ k * y ^ (n - k) * n.choose k :=
-- proof
  add_pow x y n


-- created on 2018-08-17
-- updated on 2026-10-26
