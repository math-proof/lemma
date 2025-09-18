import Lemma.Algebra.ValGet.eq.ValArraySliceFlatten
import Lemma.Algebra.Lt_Sub.of.LtAdd
import Lemma.Algebra.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub
import Lemma.Algebra.AddMul.lt.Mul
open Algebra


@[main, comm]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m)
  (j : Fin n) :
-- imply
  have := AddMul.lt.Mul i j
  v[i, j] = v.flatten[i * n + j] := by
-- proof
  intro h
  simp [GetElem.getElem]
  have h_vi : v[(i : ℕ)].val = (v.flatten.array_slice ((i : ℕ) * n) n).val := ValGet.eq.ValArraySliceFlatten v i
  have h_vi_val : v.val[(i : ℕ)].val = v[i].val := by
    simp
    simp only [GetElem.getElem]
    simp [List.Vector.get]
  simp [List.Vector.get]
  simp [h_vi_val]
  simp [h_vi]
  have h_lt : j < n ⊓ (m * n - i * n) := by
    simp_all
    apply Lt_Sub.of.LtAdd.left.nat h
  have := GetArraySlice.eq.Get_Add.of.Lt_Min_Sub h_lt v.flatten
  simp [GetElem.getElem] at this
  simp [List.Vector.get] at this
  rw [this]


-- created on 2025-05-31
-- updated on 2025-07-09
