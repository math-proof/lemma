import Lemma.Bool.EqCast.of.HEq
import Lemma.Fin.HEqFinS.of.Eq.Eq.Lt
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqValCast.of.Lt.Eq
import Lemma.Nat.Le_SubMulS.of.Lt
import Lemma.Tensor.Unsqueeze.eq.TensorMap_FunGetData
import Lemma.Vector.EqGetRange
import Lemma.Vector.EqGetS
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.GetFlatten_AddMul.eq.Get.of.Lt.Lt
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
open List Vector Nat Bool Tensor Fin


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
  obtain ⟨i, j, h_ij⟩ := Any_Eq_AddMul.of.Lt_Mul h_k
  obtain ⟨k, hk⟩ := k
  simp at h_ij
  simp [EqGetS]
  simp [h_ij]
  have h_eq : Fin ((n :: s).tail.insertIdx d 1).prod = Fin (n :: s).tail.prod := by
    simp_all
  have h_flat := GetFlatten_AddMul.eq.Get.of.Lt.Lt i.isLt j.isLt ((⟨X⟩ : Tensor α (n :: s)).toVector.map (fun X ↦ List.Vector.map (fun k ↦ X.data[cast h_eq k]) (List.Vector.range (s.insertIdx d 1).prod)))
  simp_all
  unfold Tensor.toVector
  have h_prod : X.length / n = s.prod := by
    simp [List.Vector.length]
    rw [EqDivMul.of.Ne_0.left]
    grind
  have h_bound : X.length / n ≤ n * s.prod - ↑(List.Vector.range n)[i] * (X.length / n) := by
    simp [GetElem.getElem, EqGetRange.fin i]
    simpa only [← h_prod] using! Le_SubMulS.of.Lt i.isLt (X.length / n)
  have h_get := GetCast_Map.eq.UFnGet.of.Eq.Lt.fin (i := i) (n := ((n :: s).take 1).prod) (n' := (n :: s).headD 1) (by simp_all) (by simp_all) (X.splitAt 1) (fun X ↦ (⟨X⟩ : Tensor α s))
  have h_split := GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop.fin (s := n :: s) (d := 1) (i := i) (j := (cast h_eq (List.Vector.range (s.insertIdx d 1).prod)[j]).val)
    (by simp_all) (by simp_all) X
  dsimp [Tensor.toVector] at h_flat ⊢
  simp [GetElem.getElem] at h_flat h_get h_split ⊢
  symm
  refine Eq.trans h_flat ?_
  simp [h_get]
  convert h_split
  simp [EqGetRange.fin]
  rw [EqValCast.of.Lt.Eq (by rw [h_prod_insert.symm]) h_k]
  congr 1
  have h_heq := HEqFinS.of.Eq.Eq.Lt j.isLt h_prod_insert rfl
  simpa [h_eq] using (congrArg Fin.val (EqCast.of.HEq h_heq)).symm


-- created on 2025-07-13
-- updated on 2025-11-30
