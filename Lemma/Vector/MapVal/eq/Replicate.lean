import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m) :
-- imply
  (v.val).map (List.length ∘ List.Vector.toList) = List.replicate m n := by
-- proof
  induction h : v using List.Vector.inductionOn with
  | nil =>
    rfl
  | cons ih =>
    simp_all [List.Vector.toList, List.replicate]


-- created on 2025-05-27
