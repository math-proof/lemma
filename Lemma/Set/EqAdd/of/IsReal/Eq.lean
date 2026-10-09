import Mathlib.Data.EReal.Basic
import sympy.Basic


@[path]
private lemma main
  {a : ℝ}
  {y z : EReal}
-- given
  (_h₀ : (a : EReal) ∈ Set.Ioo (⊥ : EReal) (⊤ : EReal))
  (h₁ : y - (a : EReal) = z) :
-- imply
  y = (a : EReal) + z := by
-- proof
  rw [← h₁]
  suffices key : ∀ y : EReal, y = (a : EReal) + (y - (a : EReal)) from key y
  rw [EReal.forall]
  constructor
  · simp [EReal.bot_sub, EReal.add_bot]
  · constructor
    · simp
    · intro r
      rw [← EReal.coe_sub, ← EReal.coe_add]
      exact congr_arg (fun r : ℝ => (r : EReal)) (by ring)


-- created on 2023-06-29
