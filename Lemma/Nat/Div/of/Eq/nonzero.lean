import Lemma.Nat.Div.of.Eq
import sympy.Basic
open Nat


@[main]
private lemma main
  [Div α]
  [Zero α]
  {x y d : α}
-- given
  (h₀ : d ≠ 0)
  (h₁ : x = y) :
-- imply
  x / d = y / d := by
-- proof
  have _ := h₀
  exact Div.of.Eq h₁ d


-- created on 2026-10-03
