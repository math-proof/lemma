import sympy.functions.elementary.complexes
import Lemma.Complex.Add_MulI.is.Eq.Eq


@[main]
private lemma main
  (x y a b c : ℝ)
-- given
  (h : x + I * y = a + I * (b * c)) :
-- imply
  x = a ∧ y = b * c := by
-- proof
  constructor
  · simpa using congrArg Complex.re h
  · simpa using congrArg Complex.im h


-- created on 2026-10-03
