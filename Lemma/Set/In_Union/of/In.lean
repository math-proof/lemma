import Lemma.Basic


@[main]
private lemma main
  {A : Set α}
  {e : α}
-- given
  (h : e ∈ A)
  (B : Set α)
  (left : Bool := false) :
-- imply
  match left with
  | false =>
    e ∈ A ∪ B
  | true =>
    e ∈ B ∪ A := by
-- proof
  -- Use the definition of union to rewrite the goal in terms of set membership.
  cases left <;> rw [Set.mem_union]
  ·
    -- Apply the logical OR introduction rule to the right disjunct (e ∈ A).
    exact Or.inl h
  ·
    -- Apply the logical OR introduction rule to the left disjunct (e ∈ B).
    exact Or.inr h


-- created on 2025-04-05
-- updated on 2025-04-06
