import Lemma.Bool.EqCast.of.HEq
import Lemma.Bool.HEqMkS.of.Eq.Eq.Lt
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqValCast.of.Lt.Eq
import Lemma.Nat.Le_SubMulS.of.Lt
import Lemma.Tensor.Unsqueeze.eq.TensorMap_FunGetData
import Lemma.Vector.EqGetRange
import Lemma.Vector.EqGetRange.of.Lt
import Lemma.Vector.EqGetS
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.GetFlatten_AddMul.eq.Get.of.Lt.Lt
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
open List Vector Nat Bool Tensor


@[main]
private lemma main
  {d : ℕ}
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.unsqueeze (d + 1) = Tensor.fromVector (X.toVector.map (·.unsqueeze d)) := by
-- proof
  obtain ⟨X⟩ := X
  simp [Unsqueeze.eq.TensorMap_FunGetData]
  unfold Tensor.fromVector
  simp
  ext k
  simp [EqGetRange.fin]
  have h_k := k.isLt
  have h_prod_insert := ProdInsertIdx.eq.Prod s d
  obtain ⟨i, h_i, j, h_j, h_ij⟩ := Any_Eq_AddMul.of.Lt_Mul h_k
  obtain ⟨k, hk⟩ := k
  simp at h_ij
  simp [EqGetS]
  simp [h_ij]
  have h_eq : Fin ((n :: s).tail.insertIdx d 1).prod = Fin (n :: s).tail.prod := by
    simp_all
  have := GetFlatten_AddMul.eq.Get.of.Lt.Lt h_i h_j ((⟨X⟩ : Tensor α (n :: s)).toVector.map (fun X ↦ List.Vector.map (fun k ↦ X.data[cast h_eq k]) (List.Vector.range (s.insertIdx d 1).prod)))
  simp_all
  unfold Tensor.toVector
  have h_prod : X.length / n = s.prod := by
    simp [List.Vector.length]
    rw [EqDivMul.of.Ne_0.left]
    linarith
  have : X.length / n ≤ n * s.prod - ↑(List.Vector.range n)[i] * (X.length / n) := by
    simp [h_prod]
    rw [EqGetRange.of.Lt]
    apply Le_SubMulS.of.Lt h_i
  have := GetCast_Map.eq.UFnGet.of.Eq.Lt (i := i) (n := ((n :: s).take 1).prod) (n' := (n :: s).headD 1) (by simp_all) (by simp_all) (X.splitAt 1) (fun X ↦ (⟨X⟩ : Tensor α s))
  simp at this
  simp [this]
  have := GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop (s := n :: s) (d := 1) (i := i) (j := (cast h_eq (List.Vector.range (s.insertIdx d 1).prod)[j]).val)
    (by simp_all) (by simp_all) X
  simp at this
  simp [this]
  simp [GetElem.getElem]
  congr
  apply EqCast.of.HEq
  apply HEqMkS.of.Eq.Eq.Lt
  ·
    simp_all
  ·
    simp [EqGetRange.fin]
    rw [EqValCast.of.Lt.Eq]
    ·
      assumption
    ·
      rwa [h_prod_insert] at h_j


-- created on 2025-07-13
-- updated on 2025-11-30
