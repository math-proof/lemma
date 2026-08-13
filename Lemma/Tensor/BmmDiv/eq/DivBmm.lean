import Lemma.List.EqSwap_0'1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
import Lemma.List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength
import Lemma.Tensor.CastDiv.eq.DivCast.of.Eq
import Lemma.Tensor.MulDiv.eq.DivMul
import Lemma.Tensor.RepeatDiv.eq.DivRepeat
import Lemma.Tensor.SumDiv.eq.DivSum
import Lemma.Tensor.UnsqueezeDiv.eq.DivUnsqueeze
open List Tensor


@[main]
private lemma main
  [Semifield α]
-- given
  (A : Tensor α (bz ++ [m, k]))
  (C : Tensor α (bz ++ [k, n]))
  (B : Tensor α []) :
-- imply
  (A / B).bmm C = A.bmm C / B := by
-- proof
  let A_div0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx])) ((A / B).unsqueeze (bz.length + 1))
  let A0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx])) (A.unsqueeze (bz.length + 1))
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0]
    have hu := UnsqueezeDiv.eq.DivUnsqueeze A B (bz.length + 1)
    rw [hu]
    exact CastDiv.eq.DivCast.of.Eq (by simp [InsertIdxAppend.eq.Append_InsertIdx])
      (A.unsqueeze (bz.length + 1)) B
  let A_div : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨bz.length + 1, by grind⟩ n)
  let A' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨bz.length + 1, by grind⟩ n)
  let CT : Tensor α (bz ++ [n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]
      simp [EqSwap_0'1])) Cᵀ
  let C0 : Tensor α (bz ++ [1, n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength (by simp)]
      simp))
      (CT.unsqueeze bz.length)
  let C' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨bz.length, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, RepeatDiv.eq.DivRepeat A0 B ⟨bz.length + 1, by grind⟩ n]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  have hsum : (A_div * C').sum (bz.length + 2) = (A' * C').sum (bz.length + 2) / B := by
    rw [hA, MulDiv.eq.DivMul, SumDiv.eq.DivSum]
  have hs : (bz ++ [m, n, k]).eraseIdx (bz.length + 2) = bz ++ [m, n] := by
    simp [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength]
  have hL : (A / B).bmm C = cast (congrArg (Tensor α) hs) ((A_div * C').sum (bz.length + 2)) := by
    simp [Tensor.bmm, A_div, A_div0, C', C0, CT]
  have hR : A.bmm C = cast (congrArg (Tensor α) hs) ((A' * C').sum (bz.length + 2)) := by
    simp [Tensor.bmm, A', A0, C', C0, CT]
  rw [hL, hR, hsum]
  apply CastDiv.eq.DivCast.of.Eq hs


-- created on 2026-08-13
