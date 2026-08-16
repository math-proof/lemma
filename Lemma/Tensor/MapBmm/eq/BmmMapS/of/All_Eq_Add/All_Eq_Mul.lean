import Lemma.List.EqSwap_0'1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
import Lemma.List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength
import Lemma.Tensor.MapCast.as.Map.of.Eq
import Lemma.Tensor.MapMul.eq.MulMapS.of.All_Eq_Mul
import Lemma.Tensor.RepeatMap.eq.MapRepeat
import Lemma.Tensor.SumMap.eq.MapSum.of.All_EqUFnAdd
import Lemma.Tensor.TMap.eq.MapT
import Lemma.Tensor.UnsqueezeMap.eq.MapUnsqueeze
open List Tensor


/-- `bmm` commutes with a pointwise map `f`. -/
@[main, comm]
private lemma main
  [Mul α] [AddCommMonoid α]
  [Mul β] [AddCancelCommMonoid β]
  {f : α → β}
-- given
  (h_mul : ∀ a b, f (a * b) = f a * f b)
  (h_add : ∀ a b, f (a + b) = f a + f b)
  (A : Tensor α (bz ++ [m, k]))
  (C : Tensor α (bz ++ [k, n])) :
-- imply
  (A.bmm C).map f = (A.map f).bmm (C.map f) := by
-- proof
  let F {s} (X : Tensor α s) : Tensor β s := X.map f
  let A_f0 : Tensor β (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor β) (by simp [InsertIdxAppend.eq.Append_InsertIdx])) ((F A).unsqueeze (bz.length + 1))
  let A0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx])) (A.unsqueeze (bz.length + 1))
  have h0 : A_f0 = F A0 := by
    simp only [A_f0, A0, F]
    rw [UnsqueezeMap.eq.MapUnsqueeze]
    apply Cast_Map.eq.MapCast.of.Eq
    simp [InsertIdxAppend.eq.Append_InsertIdx]
  let A_f : Tensor β (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor β) (by simp)) (A_f0.repeat ⟨bz.length + 1, by grind⟩ n)
  let A' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨bz.length + 1, by grind⟩ n)
  have hA : A_f = F A' := by
    simp only [A_f, A', F]
    rw [h0]
    simp only [F]
    rw [RepeatMap.eq.MapRepeat]
    apply Cast_Map.eq.MapCast.of.Eq
    simp
  let CT : Tensor α (bz ++ [n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]
      simp [EqSwap_0'1])) Cᵀ
  let CT_f : Tensor β (bz ++ [n, k]) :=
    cast (congrArg (Tensor β) (by
      rw [SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]
      simp [EqSwap_0'1])) (F C)ᵀ
  have hT : CT_f = F CT := by
    simp only [CT_f, CT, F]
    rw [TMap.eq.MapT]
    apply Cast_Map.eq.MapCast.of.Eq
    rw [SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]
    simp [EqSwap_0'1]
  let C0 : Tensor α (bz ++ [1, n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength (by simp)]
      simp))
      (CT.unsqueeze bz.length)
  let C0_f : Tensor β (bz ++ [1, n, k]) :=
    cast (congrArg (Tensor β) (by
      rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength (by simp)]
      simp))
      (CT_f.unsqueeze bz.length)
  have hC0 : C0_f = F C0 := by
    simp only [C0_f, C0, F]
    rw [hT]
    simp only [F]
    rw [UnsqueezeMap.eq.MapUnsqueeze]
    apply Cast_Map.eq.MapCast.of.Eq
    rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength (by simp)]
    simp
  let C' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨bz.length, by grind⟩ m)
  let C'_f : Tensor β (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor β) (by simp)) (C0_f.repeat ⟨bz.length, by grind⟩ m)
  have hC : C'_f = F C' := by
    simp only [C'_f, C', F]
    rw [hC0]
    simp only [F]
    rw [RepeatMap.eq.MapRepeat]
    apply Cast_Map.eq.MapCast.of.Eq
    simp
  have hsum : (A_f * C'_f).sum (bz.length + 2) = F ((A' * C').sum (bz.length + 2)) := by
    rw [hA, hC]
    simp only [F]
    rw [MulMapS.eq.MapMul.of.All_Eq_Mul h_mul]
    rw [MapSum.eq.SumMap.of.All_EqUFnAdd h_add]
  have hs : (bz ++ [m, n, k]).eraseIdx (bz.length + 2) = bz ++ [m, n] := by
    simp [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength]
  have hL : A.bmm C = cast (congrArg (Tensor α) hs) ((A' * C').sum (bz.length + 2)) := by
    simp [Tensor.bmm, A', A0, C', C0, CT]
  have hR : (F A).bmm (F C) = cast (congrArg (Tensor β) hs) ((A_f * C'_f).sum (bz.length + 2)) := by
    simp [Tensor.bmm, A_f, A_f0, C'_f, C0_f, CT_f, F]
  rw [hL, hR, hsum]
  simp only [F]
  rw [MapCast.eq.Cast_Map.of.Eq hs]


-- created on 2026-08-16
-- updated on 2026-08-17
