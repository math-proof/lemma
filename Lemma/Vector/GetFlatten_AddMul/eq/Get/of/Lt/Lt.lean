import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Vector.GetFlatten_AddMul.eq.Get
open Vector Nat


@[main]
private lemma main
-- given
  (h_i : i < m)
  (h_j : j < n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  have := AddMul.lt.Mul.of.Lt.Lt h_i h_j
  v.flatten[i * n + j] = v[i, j] :=
-- proof
  GetFlatten_AddMul.eq.Get v ⟨i, h_i⟩ ⟨j, h_j⟩


@[main]
private lemma fin
-- given
  (h_i : i < m)
  (h_j : j < n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  have h_ij := AddMul.lt.Mul.of.Lt.Lt h_i h_j
  v.flatten.get ⟨i * n + j, h_ij⟩ = (v.get ⟨i, h_i⟩).get ⟨j, h_j⟩ :=
-- proof
  main h_i h_j v


-- created on 2025-07-09
