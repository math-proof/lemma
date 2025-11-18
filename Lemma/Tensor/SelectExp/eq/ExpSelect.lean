import sympy.Basic
import sympy.tensor.functions


@[main, comm]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (exp X).select d i = exp (X.select d i) := by
-- proof
  sorry


-- created on 2025-11-17
