import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℤ}
  {A : ℕ → Set ℤ}
-- given
  (h : x ∉ ⋃ k < n, A k) :
-- imply
  ∀ k < n, x ∉ A k := by
-- proof
  exact fun k hk hx => h (Set.mem_iUnion₂.mpr ⟨k, hk, hx⟩)


-- created on 2020-09-09
