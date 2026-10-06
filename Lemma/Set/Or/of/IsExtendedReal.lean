import sympy.Basic
import Mathlib.Data.EReal.Inv


@[main]
private lemma main
  {x : EReal} :
-- imply
  x ∈ Set.Ioo (⊥ : EReal) (⊤ : EReal) ∨ x = ⊤ ∨ x = ⊥ := by
-- proof
  if hx : x = ⊤ then
    exact Or.inr (Or.inl hx)
  else
    if hxb : x = ⊥ then
      exact Or.inr (Or.inr hxb)
    else
      exact Or.inl ⟨bot_lt_iff_ne_bot.mpr hxb, lt_top_iff_ne_top.mpr hx⟩


-- created on 2021-05-15
-- updated on 2023-05-13
