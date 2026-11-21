import Theorem.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
open Vector Fin


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.Any_And_EqGetFlatten.of.Lt_Mul |
| fin | Vector.Any_And_EqGetFlatten.of.Lt_Mul.fin |
| val | Vector.Any_And_EqGetFlatten.of.Lt_Mul.val |
-/
@[path, fin, val]
private lemma main
-- given
  (h : t < m * n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  ∃ (i : Fin m) (j : Fin n), t = i * n + j ∧ v.flatten[t] = v[i, j] := by
-- proof
  let ⟨q, r, h⟩ := Any_Eq_AddMul.of.Lt_Mul h
  use q, r
  constructor
  .
    exact h
  .
    apply GetFlatten.eq.Get.of.Eq_AddMul h


-- created on 2025-11-02
-- updated on 2026-11-20
