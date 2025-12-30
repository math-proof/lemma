import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
-- given
  (h : j < d ⊓ n)
  (v : List.Vector α n) :
-- imply
  (v.take d)[j] = v[j] := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.take]
  cases v
  simp [List.Vector.get]


@[main]
private lemma fin
-- given
  (h : j < d ⊓ n)
  (v : List.Vector α n) :
-- imply
  (v.take d).get ⟨j, by omega⟩ = v.get ⟨j, by omega⟩ :=
-- proof
  main h v


-- created on 2025-05-31
