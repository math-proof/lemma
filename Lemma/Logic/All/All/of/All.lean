import sympy.concrete.quantifier
import Lemma.Basic


@[main]
private lemma main
  {p f : α → Prop}
-- given
  (h : ∀ x | p x, f x)
  (q : α → Prop) :
-- imply
  (∀ x | p x ∧ q x, f x) ∧ ∀ x | p x ∧ ¬q x, f x := by
-- proof
  constructor  -- Split the conjunction into two goals
  · intro x ⟨hpx, _⟩  -- Introduce x and the condition p x ∧ q x
    exact h x hpx      -- Apply hypothesis h using p x
  · intro x ⟨hpx, _⟩  -- Introduce x and the condition p x ∧ ¬q x
    exact h x hpx      -- Apply hypothesis h using p x


-- created on 2025-07-20
