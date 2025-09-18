import Lemma.Logic.Imp.is.Or_Not
open Logic


@[main]
private lemma main
  {A : Set α}
  {f : α → Prop}
-- given
  (h : ∀ x ∈ A, f x)
  (a : α) :
-- imply
  f a ∨ a ∉ A := by
-- proof
  specialize h a
  rwa [Or_Not.is.Imp]


-- created on 2025-07-29
