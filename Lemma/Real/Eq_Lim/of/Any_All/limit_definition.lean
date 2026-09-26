import Lemma.Real.EqLim.is.All_Any_All_LtAbsSub
import sympy.concrete.quantifier
import sympy.series.limits
open Real


@[main]
private lemma main
  (f : ℤ → ℝ)
  (a : ℝ)
-- given
  (h : ∀ ε > 0, ∃ N : ℤ, ∀ x | x ≥ N + 1, |f x - a| < ε) :
-- imply
  lim [x → ∞] f x = a := by
-- proof
  have h' : ∀ ε > 0, ∃ N > 0, ∀ x | x > N, |f x - a| < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N 1, lt_max_of_lt_right zero_lt_one, fun x hx => hN x (by grind)⟩
  exact EqLim.of.All_Any_All_LtAbsSub.εN.pos h'


-- created on 2026-09-26
