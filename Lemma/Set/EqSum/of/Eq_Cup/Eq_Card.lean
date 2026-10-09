import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α β : Type*}
  [AddCommMonoid β]
  [DecidableEq α]
  {n : ℕ}
  {a : ℕ → α}
  {X : Finset α}
  {f : α → β}
-- given
  (hX : Finset.image a (Finset.range n) = X)
  (hcard : X.card = n) :
-- imply
  ∑ x ∈ X, f x = ∑ i ∈ Finset.range n, f (a i) := by
-- proof
  have hinj : Set.InjOn a (Finset.range n : Set ℕ) := by
    rw [← Finset.card_image_iff, hX, hcard, Finset.card_range]
  rw [← hX, Finset.sum_image hinj]


-- created on 2021-03-21
