import sympy.Basic


@[main]
private lemma main :
-- imply
  p ∨ False ↔ p := by
-- proof
  apply Iff.intro
  focus
    intro h
    match h with
    | Or.inl hp => exact hp
    | Or.inr hf => exact hf.elim
  focus
    intro hp
    exact Or.inl hp


-- created on 2024-07-01
