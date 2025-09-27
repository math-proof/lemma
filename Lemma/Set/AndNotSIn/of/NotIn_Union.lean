import Lemma.Basic


@[main]
private lemma FIN
  [DecidableEq ι]
  {A B : Finset ι}
  {x : ι}
-- given
  (h : x ∉ A ∪ B) :
-- imply
  x ∉ A ∧ x ∉ B := by
-- proof
  -- Split the goal into two subgoals: x ∉ A and x ∉ B.
  constructor <;>
    simp_all [Finset.mem_union]


@[main]
private lemma main
  {A B : Set α}
-- given
  {x : α}
  (h : x ∉ A ∪ B) :
-- imply
  x ∉ A ∧ x ∉ B := by
-- proof
  -- Start with the given assumption x ∉ A ∪ B
  have h₀ : x ∉ A := fun hx => h (Or.inl hx)
  have h₁ : x ∉ B := fun hx => h (Or.inr hx)
  -- Combine the results to conclude x ∉ A ∧ x ∉ B
  exact ⟨h₀, h₁⟩


-- created on 2025-04-05
-- updated on 2025-04-30
