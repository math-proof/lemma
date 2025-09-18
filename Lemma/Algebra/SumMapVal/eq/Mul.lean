import stdlib.List.Vector
import Lemma.Algebra.MapVal.eq.Replicate
open Algebra


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
