import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma fin
  [Preorder α] [LocallyFiniteOrder α]
  {a b : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : x < b) :
-- imply
  x ∈ Finset.Ico a b := by
-- proof
  simp_all


/--
This lemma asserts that an element `x` is in the interval `Ico a b` (closed on the left, open on the right) if `a ≤ x` and `x < b`.
The proof combines these two inequalities to establish membership in the interval by constructing the pair `⟨h₀, h₁⟩`, where `h₀` and `h₁` are the given bounds.
-/
@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : x < b) :
-- imply
  x ∈ Ico a b :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2025-03-02
-- updated on 2025-05-18
