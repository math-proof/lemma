import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {x : ℕ → ℝ}
-- given
  (_h : ∀ i, x i > 0) :
-- imply
  alpha (List.ofFn ![x 0, x 1, x 2]) = alpha [x 0, x 1, x 2] := by
-- proof
  rfl


-- created on 2020-09-26
