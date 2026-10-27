import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Iio 0) :
-- imply
  |x| = -x :=
-- proof
  abs_of_neg h₀


-- created on 2023-04-18
