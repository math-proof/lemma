import Lemma.Set.IsReal.of.Le
open scoped ComplexOrder


@[path]
private lemma main
  {x : ℂ}
-- given
  (h : x ≤ 0) :
-- imply
  x ∈ Set.range Complex.ofReal :=
-- proof
  Set.IsReal.of.Le (b := 0) h


-- created on 2021-05-25
