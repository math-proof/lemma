import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℂ} :
-- imply
  x - ~x = 2 * im x * Complex.I := by
-- proof
  rw [Complex.conj, Complex.sub_conj]
  push_cast
  ring


-- created on 2023-05-25
