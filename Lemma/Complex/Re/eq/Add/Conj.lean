import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  (re z : ℂ) = (z + ~z) / 2 := by
-- proof
  rw [Complex.add_conj]
  push_cast
  ring


-- created on 2023-06-24
