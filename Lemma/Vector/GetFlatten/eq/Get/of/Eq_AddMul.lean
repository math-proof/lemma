import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Nat.AddMul.lt.Mul
open Vector Nat


@[main, fin, val]
private lemma main
  {i : Fin m}
  {j : Fin n}
-- given
  (h_t : t = i * n + j)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  v.flatten[t]'(by convert AddMul.lt.Mul i j) = v[i, j] := by
-- proof
  simp [h_t]
  apply GetFlatten_AddMul.eq.Get


-- created on 2025-07-06
-- updated on 2025-07-09
