import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
-- given
  (head : List.Vector α n)
  (tail : List.Vector (List.Vector α n) m) :
-- imply
  (head ::ᵥ tail).flatten.val = (head ++ tail.flatten).val := by
-- proof
  simp [List.Vector.flatten, HAppend.hAppend]
  simp [List.Vector.toList]
  simp [Append.append]
  let ⟨head, _⟩ := head
  simp


-- created on 2025-05-08
