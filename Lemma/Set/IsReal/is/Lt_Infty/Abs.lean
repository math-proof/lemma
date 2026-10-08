import sympy.Basic
import Mathlib.Data.EReal.Inv


@[main]
private lemma main
  {x : EReal}
-- given
  (h : x ∈ Set.Ioo (⊥ : EReal) (⊤ : EReal)) :
-- imply
  x.abs < (⊤ : ENNReal) := by
-- proof
  obtain ⟨h_bot, h_top⟩ := h
  rw [← EReal.coe_toReal (ne_of_lt h_top) (ne_of_gt h_bot)]
  exact EReal.abs_coe_lt_top x.toReal


-- created on 2023-04-16
