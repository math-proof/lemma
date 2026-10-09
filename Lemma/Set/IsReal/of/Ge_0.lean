import sympy.functions.elementary.complexes
import Lemma.Set.IsReal.of.Ge
import sympy.Basic
open scoped ComplexOrder


@[path]
private lemma main
  {x : ℂ}
-- given
  (h : x ≥ 0) :
-- imply
  x ∈ Set.range Complex.ofReal :=
-- proof
  Set.IsReal.of.Ge (b := 0) h


-- created on 2021-04-11
