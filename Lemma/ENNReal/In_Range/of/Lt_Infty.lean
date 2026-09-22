import Mathlib.Data.ENNReal.Real
import sympy.Basic


/--
If an ENNReal is strictly below ⊤, it comes from a real
(|x| < ∞ for nonnegative x is x < ⊤).
-/
@[main]
private lemma main
  {x : ENNReal}
-- given
  (h : x < ⊤) :
-- imply
  x ∈ Set.range ENNReal.ofReal := by
-- proof
  refine ⟨x.toReal, ?_⟩
  exact ENNReal.ofReal_toReal h.ne


-- created on 2020-04-02
