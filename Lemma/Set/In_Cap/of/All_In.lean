import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : ℕ → Set α}
  {x : α}
-- given
  (h : x ∈ ⋂ k < n, A k) :
-- imply
  ∀ k < n, x ∈ A k :=
-- proof
  fun k hk ↦ Set.mem_iInter₂.mp h k hk


-- created on 2021-01-22
