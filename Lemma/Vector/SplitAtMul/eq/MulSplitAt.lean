import sympy.Basic
import sympy.vector.vector


@[main]
private lemma main
  [Mul α]
  {s : List ℕ}
-- given
  (x : List.Vector α s.prod)
  (a : α)
  (d : ℕ):
-- imply
  (x * a).splitAt d = x.splitAt d * List.Vector.replicate (s.drop d).prod a := by
-- proof
  sorry


-- created on 2025-12-01
