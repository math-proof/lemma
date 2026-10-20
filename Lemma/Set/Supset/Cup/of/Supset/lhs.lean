import sympy.Basic


@[path]
private lemma main
  [Nonempty ι]
  {A B : Set α}
-- given
  (h₀ : B ⊆ A) :
-- imply
  (⋃ (_ : ι), B) ⊆ A := by
-- proof
  simpa [Set.iUnion_const] using h₀


-- created on 2021-07-04
-- updated on 2026-10-17
