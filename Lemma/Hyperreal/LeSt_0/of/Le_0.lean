import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x ≤ 0) :
-- imply
  stdPart x ≤ 0 := by
-- proof
  if hx : 0 ≤ ArchimedeanClass.mk x then
    have h0 := Hyperreal.archimedeanClassMk_coe_nonneg 0
    have := ArchimedeanClass.stdPart_monotoneOn (a := x) (b := (0 : ℝ*)) hx h0 h
    simpa [ArchimedeanClass.stdPart_zero] using this
  else
    rw [ArchimedeanClass.stdPart_eq_zero.mpr (ne_of_lt (lt_of_not_ge hx))]


-- created on 2025-12-11
