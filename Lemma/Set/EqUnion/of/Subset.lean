import Lemma.Set.Union
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊆ B) :
-- imply
  A ∪ B = B := by
-- proof
  -- We will show that each set is a subset of the other.
  apply Set.ext
  intro x
  -- For any element x, we need to show that x ∈ A ∪ B ↔ x ∈ B.
  constructor
  ·
    intro h'
    obtain h_A | h_B := h'
    ·
      exact h h_A
    ·
      assumption
  ·
    tauto


@[main]
private lemma left
  {A B : Set α}
-- given
  (h : B ⊆ A) :
-- imply
  A ∪ B = A := by
-- proof
  rw [Union.comm]
  apply main h


-- created on 2025-04-05
-- updated on 2025-07-20
