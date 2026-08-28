import Lemma.Nat.Eq_0.is.EqSquare_0
open Nat


/--
Ferrari's resolvent cubic for the quartic formula

[Quartic formula](https://planetmath.org/QuarticFormula)

[Quartic equation](https://en.wikipedia.org/wiki/Quartic_equation)
-/
@[main]
private lemma main
  [Field K] [CharZero K]
  {y α β γ : K}
-- given
  (h₀ : β ≠ 0)
  (h₁ : y ^ 3 - α * y ^ 2 / 2 - γ * y + (α * γ / 2 - β ^ 2 / 8) = 0) :
-- imply
  y ≠ α / 2 := by
-- proof
  intro h
  apply h₀
  apply Eq_0.of.EqSquare_0
  rw [h] at h₁
  linear_combination -8 * h₁


-- created on 2018-11-11
-- updated on 2026-08-28
