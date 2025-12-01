import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
open Vector Fin


@[main]
private lemma main
-- given
  (h : t < m * n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  ∃ (i : Fin m) (j : Fin n), t = i * n + j ∧ v.flatten[t] = v[i.val, j.val] := by
-- proof
  let ⟨q, r, h⟩ := Any_Eq_AddMul.of.Lt_Mul h
  use q, r
  constructor
  .
    exact h
  .
    apply GetFlatten.eq.Get.of.Eq_AddMul h


@[main]
private lemma fin
-- given
  (h : t < m * n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  ∃ (i : Fin m) (j : Fin n), t = i * n + j ∧ v.flatten.get ⟨t, h⟩ = (v.get i).get j :=
-- proof
  main h v


-- created on 2025-11-02
