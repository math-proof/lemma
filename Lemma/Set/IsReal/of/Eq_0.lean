import Lemma.Set.IsReal.of.Eq
import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
-- given
  (h : x = 0) :
-- imply
  x ∈ Set.range ((↑) : ℝ → ℂ) :=
-- proof
  Set.IsReal.of.Eq (e := 0) h


-- created on 2023-04-18
