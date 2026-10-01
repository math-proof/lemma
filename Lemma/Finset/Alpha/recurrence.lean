import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (_h₀ : n > 0)
  (_h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range (n + 2)).map x) = alpha ((List.range n).map x ++ [x n + 1 / x (n + 1)]) := by
-- proof
  show alpha ((List.range (n + 1 + 1)).map x) = _
  rw [List.range_succ, List.range_succ, List.map_append, List.map_append, List.append_assoc]
  exact alpha_append_pair _ _ _


-- created on 2020-09-18
