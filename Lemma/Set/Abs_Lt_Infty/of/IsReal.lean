import sympy.Basic
import Mathlib.Data.EReal.Inv


@[path]
private lemma main
  {x : EReal}
-- given
  (h₀ : x.abs < (⊤ : ENNReal)) :
-- imply
  x ∈ Set.Ioo (⊥ : EReal) (⊤ : EReal) := by
-- proof
  if hx : x = ⊤ then
    rw [hx, EReal.abs_top] at h₀
    exact absurd h₀ (lt_irrefl _)
  else
    if hxb : x = ⊥ then
      rw [hxb, EReal.abs_bot] at h₀
      exact absurd h₀ (lt_irrefl _)
    else
      exact ⟨bot_lt_iff_ne_bot.mpr hxb, lt_top_iff_ne_top.mpr hx⟩


-- created on 2023-04-16
-- updated on 2026-10-17
