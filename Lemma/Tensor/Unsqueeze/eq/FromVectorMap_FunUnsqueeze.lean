import sympy.tensor.Basic
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Vector.EqGetRange
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.EqGetS
import Lemma.Vector.GetFlatten_AddMul.eq.Get.of.Lt.Lt
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Vector.EqGetRange.of.Lt
import Lemma.Nat.Le_SubMulS.of.Lt
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Bool.EqCast.of.HEq
import Lemma.Bool.HEq.of.All_HEq.Eq
import Lemma.Bool.HEqMkS.of.Eq.Eq.Lt
import Lemma.Nat.EqValCast.of.Lt.Eq
open Vector List Bool Nat


@[main]
private lemma main
  {dim : ℕ}
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.unsqueeze (dim + 1) = Tensor.fromVector (X.toVector.map (·.unsqueeze dim)) := by
-- proof
  obtain ⟨data⟩ := X
  unfold Tensor.unsqueeze Tensor.fromVector
  simp
  ext k
  simp [EqGetRange.fin]
  have h_k := k.isLt
  have h_prod_insert := ProdInsertIdx.eq.Prod s dim
  obtain ⟨i, h_i, j, h_j, h_ij⟩ := Any_Eq_AddMul.of.Lt_Mul h_k
  obtain ⟨k, hk⟩ := k
  simp at h_ij
  simp [EqGetS]
  simp [h_ij]
  have h_eq : Fin ((n :: s).tail.insertIdx dim 1).prod = Fin (n :: s).tail.prod := by
    simp_all
  have := GetFlatten_AddMul.eq.Get.of.Lt.Lt h_i h_j ((⟨data⟩ : Tensor α (n :: s)).toVector.map (fun X ↦ List.Vector.map (fun k ↦ X.data[cast h_eq k]) (List.Vector.range (s.insertIdx dim 1).prod)))
  simp_all
  unfold Tensor.toVector
  have h_prod : data.length / n = s.prod := by
    simp [List.Vector.length]
    rw [EqDivMul.of.Ne_0.left]
    linarith
  have : data.length / n ≤ n * s.prod - ↑(List.Vector.range n)[i] * (data.length / n) := by
    simp [h_prod]
    rw [EqGetRange.of.Lt]
    apply Le_SubMulS.of.Lt h_i
  have := GetCast_Map.eq.UFnGet.of.Eq.Lt (i := i) (n := ((n :: s).take 1).prod) (n' := (n :: s).headD 1) (by simp_all) (by simp_all) (data.splitAt 1) (fun data ↦ (⟨data⟩ : Tensor α s))
  simp at this
  simp [this]
  have := GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop (s := n :: s) (d := 1) (i := i) (j := (cast h_eq (List.Vector.range (s.insertIdx dim 1).prod)[j]).val)
    (by simp_all) (by simp_all) data
  simp at this
  simp [this]
  simp [GetElem.getElem]
  congr
  apply EqCast.of.HEq
  apply HEqMkS.of.Eq.Eq.Lt
  .
    simp_all
  .
    simp [EqGetRange.fin]
    rw [EqValCast.of.Lt.Eq]
    .
      assumption
    .
      rwa [h_prod_insert] at h_j


-- created on 2025-07-13
-- updated on 2025-07-17
