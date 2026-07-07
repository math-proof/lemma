import sympy.Basic
import sympy.series.limits


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x ≥ 0) :
-- imply
  stdPart x ≥ 0 := by
-- proof
  if hx : 0 ≤ ArchimedeanClass.mk x then
    have h0 := Hyperreal.archimedeanClassMk_coe_nonneg 0
    have := ArchimedeanClass.stdPart_monotoneOn (a := (0 : ℝ*)) (b := x) h0 hx h
    simpa [ArchimedeanClass.stdPart_zero] using this
  else
    rw [ArchimedeanClass.stdPart_eq_zero.mpr]
    apply ne_of_lt
    apply lt_of_not_ge hx


-- created on 2025-12-11
