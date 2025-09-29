import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
  {i : ℕ}
-- given
  (h : i < n)
  (v : List.Vector α n):
-- imply
  have : i < v.val.length := by simp_all
  v.val[i] = v[i] :=
-- proof
  rfl


-- created on 2025-05-27
-- updated on 2025-07-03
