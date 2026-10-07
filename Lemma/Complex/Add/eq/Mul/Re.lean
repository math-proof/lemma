import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℂ} :
-- imply
  x + ~x = 2 * re x := by
-- proof
  rw [Complex.add_conj]
  push_cast
  ring


-- created on 2023-05-25
