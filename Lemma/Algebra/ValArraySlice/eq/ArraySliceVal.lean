import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
-- given
  (v : List.Vector α m)
  (i n : ℕ) :
-- imply
  (v.array_slice i n).val = v.val.array_slice i n := by
-- proof
  simp [List.Vector.array_slice]
  simp [List.array_slice]
  simp [List.Vector.drop]
  simp [List.Vector.take]
  cases v
  simp


-- created on 2025-05-18
