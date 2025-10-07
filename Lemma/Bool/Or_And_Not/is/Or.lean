import Lemma.Logic.Or_Not
open Logic


@[main]
private lemma main
  {p q : Prop} :
-- imply
  p ∨ q ∧ ¬p ↔ p ∨ q := by
-- proof
  apply Iff.intro <;>
    intro h
  ·
    -- Forward direction: Assume p ∨ (q ∧ ¬p), prove p ∨ q
    obtain h | h := h
    exact Or.inl h
    exact Or.inr h.left
  ·
    -- Backward direction: Assume p ∨ q, prove p ∨ (q ∧ ¬p)
    obtain h | h := h
    exact Or.inl h
    simp [h]
    apply Or_Not


-- created on 2025-04-18
