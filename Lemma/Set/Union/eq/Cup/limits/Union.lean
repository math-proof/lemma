import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
  {f : α → Set β} :
-- imply
  (⋃ k ∈ A, f k) ∪ (⋃ k ∈ B, f k) = ⋃ k ∈ A ∪ B, f k := by
-- proof
  ext x
  simp [Set.mem_iUnion, Set.mem_union]
  aesop


-- created on 2021-07-13
