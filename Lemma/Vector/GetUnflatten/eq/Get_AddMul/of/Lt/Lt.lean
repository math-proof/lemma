import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
open Vector Nat


@[main, comm]
private lemma main
-- given
  (h_i : i < m)
  (h_j : j < n)
  (v : List.Vector α (m * n)) :
-- imply
  have := AddMul.lt.Mul.of.Lt.Lt h_i h_j
  v.unflatten[i, j] = v[i * n + j] :=
-- proof
  GetUnflatten.eq.Get_AddMul v ⟨i, h_i⟩ ⟨j, h_j⟩


-- created on 2025-07-09
