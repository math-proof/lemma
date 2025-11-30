import sympy.vector.vector
import sympy.Basic


@[main]
private lemma fin
-- given
  (h : j < d ⊓ n)
  (v : List.Vector α n) :
-- imply
  (v.take d).get ⟨j, by omega⟩ = v.get ⟨j, by omega⟩ := by
-- proof
  simp [List.Vector.take]
  cases v
  simp [List.Vector.get]


@[main]
private lemma main
-- given
  (h : j < d ⊓ n)
  (v : List.Vector α n) :
-- imply
  (v.take d)[j] = v[j] := by
-- proof
  apply fin


-- created on 2025-05-31
