import sympy.functions.elementary.complexes
import Lemma.Set.IsReal.of.Le
import sympy.Basic
open scoped ComplexOrder


@[main]
private lemma main
  {x : ℂ}
-- given
  (h : x ≤ 0) :
-- imply
  x ∈ Set.range Complex.ofReal :=
-- proof
  Set.IsReal.of.Le (b := 0) h


-- created on 2021-05-25
