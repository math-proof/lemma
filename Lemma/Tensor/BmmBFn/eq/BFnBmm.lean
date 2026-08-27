import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
import Lemma.List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength
import Lemma.Tensor.MapCast.as.MapBFn.of.Eq
import Lemma.Tensor.RepeatBFn.eq.BFnRepeat
import Lemma.Tensor.UnsqueezeBFn.eq.BFnUnsqueeze
open List Tensor


/-- `bmm` commutes with a pointwise scalar binary operator `f`. -/
@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {f : α → α → α}
-- given
  (h_mul : ∀ {s : List ℕ} (X C : Tensor α s) (B : Tensor α []),
    X.map (f · B.data[0]) * C = (X * C).map (f · B.data[0]))
  (h_sum : ∀ {s : List ℕ} (X : Tensor α s) (B : Tensor α []) (dim : ℕ),
    (X.map (f · B.data[0])).sum dim = (X.sum dim).map (f · B.data[0]))
  (A : Tensor α (bz ++ [m, k]))
  (C : Tensor α (bz ++ [k, n]))
  (B : Tensor α []) :
-- imply
  (A.map (f · B.data[0])).bmm C = (A.bmm C).map (f · B.data[0]) := by
-- proof
  let F {s} (X : Tensor α s) : Tensor α s := X.map (f · B.data[0])
  let A_f0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx])) ((F A).unsqueeze (bz.length + 1))
  let A0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx])) (A.unsqueeze (bz.length + 1))
  have h0 : A_f0 = F A0 := by
    simp only [A_f0, A0]
    rw [UnsqueezeBFn.eq.BFnUnsqueeze]
    apply Cast_MapBFn.eq.MapCast.of.Eq
    simp [InsertIdxAppend.eq.Append_InsertIdx]
  let A_f : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A_f0.repeat ⟨bz.length + 1, by grind⟩ n)
  let A' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨bz.length + 1, by grind⟩ n)
  let CT : Tensor α (bz ++ [n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]
      simp)) Cᵀ
  let C0 : Tensor α (bz ++ [1, n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength (by simp)]
      simp))
      (CT.unsqueeze bz.length)
  let C' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨bz.length, by grind⟩ m)
  have hA : A_f = F A' := by
    simp only [A_f, A']
    rw [h0, RepeatBFn.eq.BFnRepeat]
    apply Cast_MapBFn.eq.MapCast.of.Eq
    simp
  have hsum : (A_f * C').sum (bz.length + 2) = F ((A' * C').sum (bz.length + 2)) := by
    rw [hA, h_mul, h_sum]
  have hs : (bz ++ [m, n, k]).eraseIdx (bz.length + 2) = bz ++ [m, n] := by
    simp [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength]
  have hL : (F A).bmm C = cast (congrArg (Tensor α) hs) ((A_f * C').sum (bz.length + 2)) := by
    simp [Tensor.bmm, A_f, A_f0, C', C0, CT]
  have hR : A.bmm C = cast (congrArg (Tensor α) hs) ((A' * C').sum (bz.length + 2)) := by
    simp [Tensor.bmm, A', A0, C', C0, CT]
  rw [hL, hR, hsum]
  apply Cast_MapBFn.eq.MapCast.of.Eq
  assumption


-- created on 2026-08-15
