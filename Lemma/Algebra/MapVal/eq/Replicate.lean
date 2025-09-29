import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m) :
-- imply
  (v.val).map (List.length ∘ List.Vector.toList) = List.replicate m n := by
-- proof
  induction v using List.Vector.inductionOn
  case nil =>
    simp [List.replicate]
    rfl
  case cons h t ih =>
    simp_all [List.Vector.toList, List.replicate]

-- created on 2025-05-27
