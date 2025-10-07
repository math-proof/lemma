import sympy.concrete.quantifier
import Lemma.Logic.Imp.of.AllSetOf
import Lemma.Logic.Imp.of.Imp.Imp
open Logic


@[main]
private lemma main
  {p q p' q' : α → Prop}
-- given
  (h₀ : ∀ x, q' x → q x)
  (h₁ : ∀ x | q x, p x)
  (h₂ : ∃ x | q' x, p' x) :
-- imply
  ∃ x | q' x, p x ∧ p' x := by
-- proof
  let ⟨x, h_q', h_p'⟩ := h₂
  have := Imp.of.AllSetOf h₁ x
  have h_p := (Imp.of.Imp.Imp (h₀ x) this) h_q'
  use x


-- created on 2025-04-28
-- updated on 2025-05-01
