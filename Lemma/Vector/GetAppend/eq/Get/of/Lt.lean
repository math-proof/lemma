import sympy.vector.vector
import Lemma.Vector.GetAppend.eq.Get
open Vector


@[main]
private lemma main
-- given
  (h : i < n)
  (a : List.Vector α n)
  (b : List.Vector α m) :
-- imply
  (a ++ b)[i] = a[i] := by
-- proof
  let i : Fin n := ⟨i, h⟩
  have := GetAppend.eq.Get a b i
  simp_all
  assumption


-- created on 2025-05-31
