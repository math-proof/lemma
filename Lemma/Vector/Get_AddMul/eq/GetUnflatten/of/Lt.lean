import Lemma.Nat.AddMul.lt.Mul
import Lemma.Nat.AddMul.lt.Mul.of.Lt
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
open Vector Nat


@[main]
private lemma main
-- given
  (h : i < m)
  (v : List.Vector α (m * n))
  (j : Fin n) :
-- imply
  have := AddMul.lt.Mul.of.Lt h j
  v[i * n + j] = v.unflatten[i, j] := by
-- proof
  let i : Fin m := ⟨i, h⟩
  have := Get_AddMul.eq.GetUnflatten v i j
  simp_all
  assumption


-- created on 2025-05-31
-- updated on 2025-07-09
