import sympy.vector.vector
import Lemma.Vector.MapVal.eq.Replicate
open Vector


@[main]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m) :
-- imply
  ((v.val).map (List.length ∘ List.Vector.toList)).sum = m * n := by
-- proof
  have := MapVal.eq.Replicate v
  simp_all [List.sum_replicate]


-- created on 2025-05-27
