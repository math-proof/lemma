import Lemma.Vector.Get.eq.GetFlatten_AddMul
import Lemma.Algebra.AddMul.lt.Mul
open Algebra Vector


@[main]
private lemma main
  {i : Fin m}
  {j : Fin n}
-- given
  (h_t : t = i * n + j)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  have : t < m * n := by convert AddMul.lt.Mul i j
  v.flatten[t] = v[i, j] := by
-- proof
  simp [h_t]
  apply GetFlatten_AddMul.eq.Get


@[main]
private lemma fin
  {i : Fin m}
  {j : Fin n}
-- given
  (h_t : t = i * n + j)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  have h_t : t < m * n := by convert AddMul.lt.Mul i j
  v.flatten.get ⟨t, h_t⟩ = (v.get i).get j := by
-- proof
  apply main
  assumption


-- created on 2025-07-06
-- updated on 2025-07-09
