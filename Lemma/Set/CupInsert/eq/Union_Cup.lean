import sympy.Basic


@[main]
private lemma main
-- given
  (a : α)
  (s : Set α)
  (f : α → Set β) :
-- imply
  ⋃ x ∈ insert a s, f x = f a ∪ ⋃ x ∈ s, f x :=
-- proof
  Set.biUnion_insert a s f


-- created on 2020-07-03
-- updated on 2026-09-08
