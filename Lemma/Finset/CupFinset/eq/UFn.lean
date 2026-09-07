import sympy.Basic


@[main]
private lemma fn
  [DecidableEq α]
-- given
  (f : α → Finset β)
  (a : α) :
-- imply
  ⋃ k ∈ ({a} : Finset α), f k = (f a : Set β) := by
-- proof
  simp


@[main]
private lemma main
  [DecidableEq α]
-- given
  (f : α → Set β)
  (a : α) :
-- imply
  ⋃ k ∈ ({a} : Finset α), f k = f a := by
-- proof
  simp


-- created on 2025-12-30
