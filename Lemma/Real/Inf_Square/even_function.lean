import sympy.sets.sets
import sympy.Basic
import Lemma.Real.Inf.of.Eq.even_function


open scoped Pointwise


@[path]
private lemma main
  {S : Set ℝ} :
-- imply
  sInf ((fun x => x ^ 2) '' (-S)) = sInf ((fun x => x ^ 2) '' S) :=
-- proof
  Real.Inf.of.Eq.even_function (f := fun x : ℝ => x ^ 2) (fun x => by ring)


-- created on 2019-09-18
-- updated on 2022-04-03
