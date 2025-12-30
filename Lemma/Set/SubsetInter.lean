import Lemma.Set.Inter
open Set


@[main]
private lemma main
-- given
  (A B : Set α) :
-- imply
  A ∩ B ⊆ B := by
-- proof
  intro x hx
  let ⟨hxA, hxB⟩ := hx
  exact hxB


@[main]
private lemma left
-- given
  (A B : Set α) :
-- imply
  A ∩ B ⊆ A := by
-- proof
  have := main B A
  rwa [Inter.comm] at this


-- created on 2025-04-08
-- updated on 2025-08-13
