import Def.Data.Holor.Reshape
import Def.Data.Holor.Prod
import Lemma.List.Cons_Append_List.eq.AppendTake_Length
import Lemma.List.SetAppend.eq.Append_Set.of.LeLength
import Lemma.Tensor.Einsum.as.SelectBmm.of.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.GeLength_2.GeLength_2
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetSelect.as.SelectGet.of.GtGet_0.GtGet_Add_1.LtAdd_1Length
import Lemma.Tensor.GetTensordot.as.MatmulGet.of.GtLength_0
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.Tensordot.as.Matmul
open Bool List Tensor
set_option maxHeartbeats 500000


private lemma cast_tail
  (batch : List ℕ)
  (m k' : ℕ)
  (hbatch : 0 < batch.length) :
  broadcast_shape batch.tail batch.tail ++ [m, k'] = (broadcast_shape batch [] ++ [m, k']).tail := by
  simp [broadcast_shape, hbatch]
  rw [List.tail_append_of_ne_nil (by
    intro h
    simp [h] at hbatch)]


private lemma get_xb
  [Zero α]
-- given
  (s₀ : ℕ)
  (X : Tensor α (n :: ((s₀ :: s) ++ [k])))
  (i : Fin n) :
-- imply
  let sX := n :: ((s₀ :: s) ++ [k])
  let batch := sX.take (sX.length - 2)
  let m := sX.get ⟨sX.length - 2, by simp [sX]⟩
  let last := sX.get ⟨sX.length - 1, by simp [sX]⟩
  let Xb : Tensor α (batch ++ [m, last]) :=
    cast (congrArg (Tensor α) (Eq.symm (EqAppendTake__ListGet.of.GeLength_2 (by simp [sX])))) X
  let sXi := (s₀ :: s) ++ [k]
  let batchi := sXi.take (sXi.length - 2)
  let mi := sXi.get ⟨sXi.length - 2, by simp [sXi]⟩
  let lasti := sXi.get ⟨sXi.length - 1, by simp [sXi]⟩
  let Xi := X.get ⟨i, i.isLt⟩
  let Xib : Tensor α (batchi ++ [mi, lasti]) :=
    cast (congrArg (Tensor α) (Eq.symm (EqAppendTake__ListGet.of.GeLength_2 (by simp [sXi])))) Xi
  Xb.get ⟨i.val, by
    have hcons : batch = n :: ((s₀ :: (s ++ [k])).take s.length) := by simp [sX, batch]
    grind⟩ ≃ Xib := by
-- proof
  intro sX batch m last Xb sXi batchi mi lasti Xi Xib
  have h1 := GetCast.as.Get.of.Eq.GtLength_0.fin (by simp)
    (Eq.symm (EqAppendTake__ListGet.of.GeLength_2 (by simp))) X ⟨i.val, i.isLt⟩
  apply h1.trans
  dsimp only [Xib]
  apply SEq.symm
  have hsXi : sXi.length ≥ 2 := by simp [sXi]
  apply SEqCast.of.SEq.Eq (Eq.symm (EqAppendTake__ListGet.of.GeLength_2 hsXi))
  rfl


private lemma tail
  [Mul α] [Add α] [Zero α]
-- given
  (s₀ : ℕ)
  (X : Tensor α (n :: ((s₀ :: s) ++ [k])))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  let sX := n :: ((s₀ :: s) ++ [k])
  let batch := sX.take (sX.length - 2)
  let m := sX.get ⟨sX.length - 2, by simp [sX]⟩
  let last := sX.get ⟨sX.length - 1, by simp [sX]⟩
  let v := last ⊔ n'
  let Xb : Tensor α (batch ++ [m, last]) :=
    cast (congrArg (Tensor α) (Eq.symm (EqAppendTake__ListGet.of.GeLength_2 (by simp [sX])))) X
  let hXr : (batch ++ [m, last]).set (batch.length + 1) v = batch ++ [m, v] := by
    rw [SetAppend.eq.Append_Set.of.LeLength (by simp)]
    simp
  let Xr : Tensor α (batch ++ [m, v]) := cast (congrArg (Tensor α) hXr) (Xb.resize ⟨batch.length + 1, by simp⟩ v)
  let Yr : Tensor α [v, k'] := cast (by simp) (Y.resize (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2) v)
  let sXi := (s₀ :: s) ++ [k]
  let batchi := sXi.take (sXi.length - 2)
  let mi := sXi.get ⟨sXi.length - 2, by simp [sXi]⟩
  let lasti := sXi.get ⟨sXi.length - 1, by simp [sXi]⟩
  let Xi := X.get ⟨i, i.isLt⟩
  let Xib : Tensor α (batchi ++ [mi, lasti]) :=
    cast (congrArg (Tensor α) (Eq.symm (EqAppendTake__ListGet.of.GeLength_2 (by simp [sXi])))) Xi
  let Xir : Tensor α (batchi ++ [mi, v]) := cast (by simp) (Xib.resize ⟨batchi.length + 1, by simp⟩ v)
  (Tensor.tensordot (s := batch) (s' := []) (m := m) (n := v) (k := k') Xr Yr).get ⟨i, by grind [broadcast_shape, Tensor.length]⟩
    ≃
  Tensor.tensordot (s := batchi) (s' := []) (m := mi) (n := v) (k := k') Xir Yr := by
-- proof
  intro sX batch m last v Xb hXr Xr Yr sXi batchi mi lasti Xi Xib Xir
  have h_min_length : s.length ⊓ (s.length + 1 + 1) = s.length := by omega
  have hbatch : 0 < batch.length := by simp [sX, batch]
  erw [GetTensordot.eq.Cast_MatmulGet.of.GtLength_0.fin hbatch _ _ ⟨i, by simp [sX, batch]⟩]
  simp [Tensordot.eq.Cast_Matmul]
  apply SEqCastS.of.SEq.Eq.Eq
  ·
    exact cast_tail batch m k' hbatch
  ·
    simp [broadcast_shape]
    split_ifs
    repeat simp_all
  ·
    apply SEqMatmulS.of.SEq.SEq.Eq.Eq (by simp [sX, sXi, m, mi]) (by rfl) (by simp [sX, batch])
    apply SEqCastS.of.SEq.Eq.Eq (by simp [sX, batch]) (by simp)
    dsimp only [Xr]
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i.val, by simp [sX, batch]⟩) (by simp) hXr]
    apply SEqCast.of.SEq.Eq (by simp [sX, batch])
    simp
    rw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by simp) (by simp [sX, batch]) (d := ⟨batch.length + 1, by simp⟩)]
    simp
    apply SEqCast.of.SEq.Eq (by simp [sX, batch, m])
    apply SEqResizeS.of.SEq.Val.Eq (by simp) (by simp [sX, batch, sXi, batchi])
    exact get_xb s₀ X i
    have ht : batch.tail = batchi := by simp [sX, batch, sXi, batchi]
    apply SEqReshapeS.of.Eq.Eq.Dvd (h_s := by simp [ht]) (h := rfl)


private lemma shape_eq
  (s₀ k n' k' : ℕ)
  (s : List ℕ) :
  broadcast_shape ((s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 - 2)) [] ++
      [(s₀ :: (s ++ [k]))[(s ++ [k]).length + 1 - 2]'(by simp), k'] =
    matmul_shape (s₀ :: (s ++ [k])) [n', k'] := by
  simp [matmul_shape, broadcast_shape]


@[path, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s with
  | [] =>
    conv_lhs => erw [GetDot.eq.DotGet.fin]
    rfl
  | s₀ :: s =>
    have h_min_length : s.length ⊓ (s.length + 1 + 1) = s.length := by omega
    dsimp only [Dot.dot]
    have := Einsum.eq.Cast_Tensordot.of.GeLength_2.GeLength_2 (by simp) (by simp) X Y
    erw [Get.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩]
    conv_rhs => erw [Einsum.eq.Cast_Tensordot.of.GeLength_2.GeLength_2 (by simp) (by simp)]
    simp
    clear this
    apply SEq_Cast.of.SEq.Eq (shape_eq s₀ k n' k' s)
    exact tail s₀ X Y i


@[path, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by simp) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s with
  | [] =>
    erw [GetDot.eq.DotGet.une.fin]
    rfl
  | s₀ :: s =>
    dsimp only [Dot.dot]
    rw [Einsum.eq.Cast_SelectBmm.of.GeLength_2 (by simp)]
    conv_rhs => erw [Einsum.eq.Cast_SelectBmm.of.GeLength_2 (by simp)]
    simp
    apply SEq_Cast.of.SEq.Eq
    ·
      simp [matmul_shape]
      simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
    ·
      conv_lhs => rw [show i = ⟨i, by simp⟩ by grind]
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin]
      ·
        apply SEqCast.of.SEq.Eq
        ·
          simp [AppendTake_Length.eq.Cons_Append_List]
          simp [matmul_shape]
          grind
        ·
          rw [GetSelect.eq.Cast_SelectGet.of.GtGet_0.GtGet_Add_1.LtAdd_1Length]
          ·
            apply SEqCast.of.SEq.Eq
            ·
              simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]
            ·
              apply SEqSelectS.of.SEq
              have h_bz : (n :: s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 + 1 - 2) = n :: (s₀ :: (s ++ [k])).take s.length := by
                simp
              rw [GetBmm.eq.Cast_BmmGetS.of.Eq.fin h_bz]
              apply SEqCast.of.SEq.Eq
              ·
                simp [AppendTake_Length.eq.Cons_Append_List]
              ·
                apply SEqBmmS.of.SEq.SEq
                ·
                  apply SEq_Cast.of.SEq.Eq (by simp)
                  ·
                    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by simp) (by simp)]
                    apply SEqCast.of.SEq.Eq (by simp)
                    rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by simp) (by simp)]
                    apply SEqCast.of.SEq.Eq (by simp)
                    rw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by simp) (by grind) (d := ⟨((n :: s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 + 1 - 2)).length + 1, by grind⟩)]
                    apply SEqCast.of.SEq.Eq (by simp)
                    simp
                    apply SEqResizeS.of.SEq.Val.Eq (by simp) (by simp)
                    have h_cons := Cons_Append_List.eq.AppendTake_Length s s₀ k k
                    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by grind⟩) (by grind) (by simpa)]
                    simp
                    apply SEqCastS.of.SEq.Eq.Eq (by simpa) (by simpa) (by rfl)
                ·
                  rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (by simp) (by simp)]
                  apply SEqCast.of.SEq.Eq (by simp)
                  erw [GetReshape.eq.Cast_Reshape.of.Prod.GtLength_0.fin (by grind) (by grind) (i := ⟨i, by grind⟩)]
                  apply SEqCast.of.SEq.Eq (by simp)
                  apply SEqReshapeS.of.Eq.Eq.Dvd
                  ·
                    simp
                  ·
                    rfl
          ·
            simp [AppendTake_Length.eq.Cons_Append_List]
          ·
            simp [AppendTake_Length.eq.Cons_Append_List]
      ·
        simp [matmul_shape]
      ·
        simp [matmul_shape]
        simp [EraseIdx.eq.Append_Drop_Add_1, AppendTake_Length.eq.Cons_Append_List]


-- created on 2026-01-13
