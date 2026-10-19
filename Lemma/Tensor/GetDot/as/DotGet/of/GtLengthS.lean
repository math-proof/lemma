import Lemma.List.SetAppend.eq.Append_Set.of.LeLength
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetEinsum.as.EinsumGet.of.GtLengthS
import Lemma.Tensor.GetTensordot.as.MatmulGet.of.GtLength_0
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
  (sₐ k n' k' : ℕ)
  (sₜ : List ℕ) :
  broadcast_shape ((sₐ :: (sₜ ++ [k])).take ((sₜ ++ [k]).length + 1 - 2)) [] ++
      [(sₐ :: (sₜ ++ [k]))[(sₜ ++ [k]).length + 1 - 2]'(by simp), k'] =
    matmul_shape (sₐ :: (sₜ ++ [k])) [n', k'] := by
  simp [matmul_shape, broadcast_shape]


@[path, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length > s'.length)
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α (s' ++ [n', k']))
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.GeLengthS (by grind) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s, s' with
  | [], [] =>
    conv_lhs => erw [GetDot.eq.DotGet.fin]
    rfl
  | sₐ :: sₜ, [] =>
    have h_min_length : sₜ.length ⊓ (sₜ.length + 1 + 1) = sₜ.length := by omega
    simp [Dot.dot]
    have := Einsum.eq.Cast_Tensordot.of.GeLength_2.GeLength_2 (by simp) (by simp) X Y
    erw [Get.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩]
    conv_rhs => erw [Einsum.eq.Cast_Tensordot.of.GeLength_2.GeLength_2 (by simp) (by simp)]
    simp
    clear this
    apply SEq_Cast.of.SEq.Eq (shape_eq sₐ k n' k' sₜ)
    exact tail sₐ X Y i
  | sₐ :: sₜ, s'ₐ :: s'ₜ =>
    simp [Dot.dot]
    have := GetEinsum.as.EinsumGet.of.GtLengthS.fin (by grind) X Y i
    simpa


-- created on 2026-07-16
-- updated on 2026-08-14
