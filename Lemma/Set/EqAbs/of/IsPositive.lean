import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Ioi 0) :
-- imply
  |x| = x :=
-- proof
  abs_of_pos h₀


-- created on 2023-04-18
