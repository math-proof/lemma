import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.PowPow_Div1'3'3.eq.Self
open Complex


/-- `A ^ 3 + B ^ 3 = -q`. -/
@[main]
private lemma main
  {q δ : ℂ} :
-- imply
  ((δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ)) ^ 3 + ((-δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ)) ^ 3 = -q := by
-- proof
  rw [PowPow_Div1'3'3.eq.Self, PowPow_Div1'3'3.eq.Self]
  ring


-- created on 2026-10-07
