import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Vector.GetFlatten_AddMul.eq.Get
open Vector Nat


@[main, fin]
private lemma main
-- given
  (h_i : i < m)
  (h_j : j < n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  v.flatten[i * n + j]'(AddMul.lt.Mul.of.Lt.Lt h_i h_j) = v[i, j] :=
-- proof
  GetFlatten_AddMul.eq.Get v ⟨i, h_i⟩ ⟨j, h_j⟩


-- created on 2025-07-09
