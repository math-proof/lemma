import Lemma.Nat.EqMin_SubMulS
import Lemma.Vector.GetUnflatten.eq.Cast_ArraySlice
open Vector Nat


@[main]
private lemma main
-- given
  (h : i < m)
  (v : List.Vector α (m * n)) :
-- imply
  v.unflatten[i] = cast (by rw [EqMin_SubMulS m n ⟨i, h⟩]) (v.array_slice (i * n) n) := by
-- proof
  have := GetUnflatten.eq.Cast_ArraySlice v ⟨i, h⟩
  simp_all


-- created on 2025-07-15
