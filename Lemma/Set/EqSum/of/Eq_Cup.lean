import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [DecidableEq α]
  [AddCommMonoid β]
  {n : ℕ}
  {a : ℕ → α}
  {X : Finset α}
  {f : α → β}
-- given
  (h₀ : (Finset.range n).biUnion (fun i => ({a i} : Finset α)) = X)
  (h₁ : ∀ i < n, ∀ j < n, i ≠ j → a i ≠ a j) :
-- imply
  ∑ x ∈ X, f x = ∑ i ∈ Finset.range n, f (a i) := by
-- proof
  rw [← h₀, Finset.sum_biUnion]
  ·
    simp
  ·
    intro i hi j hj hne
    simp only [Function.onFun]
    rw [Finset.disjoint_iff_ne]
    intro u hu v hv
    simp only [Finset.mem_singleton] at hu hv
    grind


-- created on 2021-03-21
-- updated on 2026-10-17
