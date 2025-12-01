import sympy.Basic
import sympy.vector.vector


@[main]
private lemma main
  [Mul α]
-- given
  (x : List.Vector α n)
  (a : α)
  (d : ℕ) :
-- imply
  (x * a).repeat d = x.repeat d * a := by
-- proof
  sorry


-- created on 2025-12-01
