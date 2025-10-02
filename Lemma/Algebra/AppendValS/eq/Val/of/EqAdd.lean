import sympy.vector.vector
import Lemma.Algebra.AppendValS.eq.Val
open Algebra


@[main]
private lemma main
-- given
  (h : m + n = N)
  (v : List.Vector α N) :
-- imply
  (v.take m).val ++ (v.drop m).val = v.val := by
-- proof
  let v' : List.Vector α (m + n) := cast (by rw [h]) v
  have := AppendValS.eq.Val v'
  have h_v : v'.val = v.val := by
    congr
    ·
      rw [h]
    ·
      simp [v']
  rw [h_v] at this
  simp [List.Vector.take, List.Vector.drop] at *
  cases v'
  cases v
  simp


-- created on 2025-05-09
