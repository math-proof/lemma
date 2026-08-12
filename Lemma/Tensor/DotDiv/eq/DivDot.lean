import Lemma.Tensor.Div.eq.Div_GetData_0
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.Dot.as.SumMul
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SumMul.of.Lt
import Lemma.Tensor.Dot.eq.SumMul.of.Ge
import Lemma.Tensor.Dot.eq.SelectDot_Unsqueeze_1
import Lemma.Tensor.Einsum.eq.MulGetData_0
import Lemma.Tensor.Einsum.eq.SumMulDataS.of.Gt
import Lemma.Tensor.Einsum.eq.SumMulDataS.of.Lt
import Lemma.Tensor.Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.EqGet_SubLength_1.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GeGet_SubLength_1.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.LtGet_SubLength_1.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.as.MatmulResizeS.of.Length.GtLength_0
import Lemma.Tensor.GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
import Lemma.Tensor.MulDiv.eq.DivMul
import Lemma.Tensor.RepeatDiv.eq.DivRepeat
import Lemma.Tensor.ReshapeDiv.eq.DivReshape.of.Dvd
import Lemma.Tensor.ResizeDiv.eq.DivResize
import Lemma.Tensor.SelectDiv.eq.DivSelect
import Lemma.Tensor.SEqTensordotS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.SumDiv.eq.DivSum
import Lemma.Tensor.Tensordot.as.Matmul.of.GeLengthS
import Lemma.Tensor.Tensordot.as.Matmul.of.LtLengthS
import Lemma.Tensor.UnsqueezeDiv.eq.DivUnsqueeze
open Tensor
set_option maxHeartbeats 8000000


private lemma vector_vector
  [Semifield α]
-- given
  (A C : Tensor α [n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  repeat rw [Dot.eq.SumMul__0]
  rw [MulDiv.eq.DivMul]
  apply SumDiv.eq.DivSum


private lemma vector_vector_lt
  [Semifield α]
-- given
  (h : n < n')
  (A : Tensor α [n])
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  rw [Einsum.eq.SumMulDataS.of.Lt h (X := A / B) (Y := C)]
  rw [Einsum.eq.SumMulDataS.of.Lt h (X := A) (Y := C)]
  have h_cast : (cast (by simp) ((A / B).resize ⟨0, by simp⟩ n') : Tensor α [n']) = (cast (by simp) (A.resize ⟨0, by simp⟩ n') : Tensor α [n']) / B := by
    rw [ResizeDiv.eq.DivResize]
    apply CastDiv.eq.DivCast.of.Eq
    simp
  erw [h_cast]
  rw [MulDiv.eq.DivMul]
  exact SumDiv.eq.DivSum _ B 0


private lemma vector_vector_gt
  [Semifield α]
-- given
  (h : n > n')
  (A : Tensor α [n])
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  rw [Einsum.eq.SumMulDataS.of.Gt h (X := A / B) (Y := C)]
  rw [Einsum.eq.SumMulDataS.of.Gt h (X := A) (Y := C)]
  have h_mul :
      (A / B) * (cast (by simp) (C.resize ⟨0, by simp⟩ n) : Tensor α [n]) =
        (A * (cast (by simp) (C.resize ⟨0, by simp⟩ n) : Tensor α [n])) / B :=
    MulDiv.eq.DivMul A _ B
  erw [h_mul]
  exact SumDiv.eq.DivSum _ B 0


private lemma left_nil
  [Semifield α]
-- given
  (A : Tensor α [])
  (B : Tensor α [])
  (C : Tensor α s') :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  rw [Einsum.eq.MulGetData_0 (X := A / B), Einsum.eq.MulGetData_0 (X := A)]
  have h : (A / B).data[0] = A.data[0] / B.data[0] := by
    simp [HDiv.hDiv]
    rfl
  rw [h]
  refine (MulDiv.eq.DivMul.left (A.data[0]) B.data[0] C).trans ?_
  rfl


private lemma right_nil
  [Semifield α]
-- given
  (A : Tensor α (n :: s))
  (B : Tensor α [])
  (C : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  unfold einsum
  have h_mul : (A / B) * C.data[0] = (A * C.data[0]) / B := by
    rw [Div.eq.Div_GetData_0 A B, Div.eq.Div_GetData_0 (A * C.data[0]) B]
    exact MulDiv.eq.DivMul.right A C.data[0] B.data[0]
  refine Eq.trans (congrArg (cast (by simp [matmul_shape])) h_mul) ?_
  apply CastDiv.eq.DivCast.of.Eq
  simp [matmul_shape]


private lemma matrix_matrix
  [Semifield α]
-- given
  (A : Tensor α [m, k])
  (C : Tensor α [k, n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let A_div0 : Tensor α [m, 1, k] := (A / B).unsqueeze 1
  let A_div : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ n)
  let A0 : Tensor α [m, 1, k] := A.unsqueeze 1
  let A' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let CT : Tensor α [n, k] := Cᵀ
  let C0 : Tensor α [1, n, k] := CT.unsqueeze 0
  let C' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hL : (A / B) @ C = (A_div * C').sum 2 := by
    simpa [A_div, A_div0, C', C0, CT] using Dot.eq.SumMul (A / B) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, C', C0, CT] using Dot.eq.SumMul A C
  rw [hL, hR]
  have hA : A_div = A' / B := by
    have h0 : A_div0 = A0 / B := by
      simp only [A_div0, A0]
      convert UnsqueezeDiv.eq.DivUnsqueeze A B 1 <;> simp
    simp only [A_div, A']
    rw [h0]
    have hr := RepeatDiv.eq.DivRepeat A0 B ⟨1, by grind⟩ n
    rw [hr]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  rw [hA, MulDiv.eq.DivMul]
  exact SumDiv.eq.DivSum _ B 2


private lemma matrix_matrix_lt
  [Semifield α]
-- given
  (h : k' < k)
  (A : Tensor α [m, k'])
  (C : Tensor α [k, n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let A_div_r : Tensor α [m, k] := (A / B).resize ⟨1, by grind⟩ k
  let A_r : Tensor α [m, k] := A.resize ⟨1, by grind⟩ k
  have hr : A_div_r = A_r / B := by
    simp only [A_div_r, A_r]
    exact ResizeDiv.eq.DivResize A B ⟨1, by grind⟩ k
  let A_div0 : Tensor α [m, 1, k] := A_div_r.unsqueeze 1
  let A0 : Tensor α [m, 1, k] := A_r.unsqueeze 1
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0, hr]
    convert UnsqueezeDiv.eq.DivUnsqueeze A_r B 1 <;> simp
  let A_div : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ n)
  let A' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let CT : Tensor α [n, k] := Cᵀ
  let C0 : Tensor α [1, n, k] := CT.unsqueeze 0
  let C' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, RepeatDiv.eq.DivRepeat A0 B ⟨1, by grind⟩ n]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  have hL : (A / B) @ C = (A_div * C').sum 2 := by
    simpa [A_div, A_div0, A_div_r, C', C0, CT] using Dot.eq.SumMul.of.Lt h (A / B) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, A_r, C', C0, CT] using Dot.eq.SumMul.of.Lt h A C
  rw [hL, hR, hA, MulDiv.eq.DivMul]
  exact SumDiv.eq.DivSum _ B 2


private lemma matrix_matrix_ge
  [Semifield α]
-- given
  (h : k ≥ k')
  (A : Tensor α [m, k])
  (C : Tensor α [k', n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let A_div0 : Tensor α [m, 1, k] := (A / B).unsqueeze 1
  let A0 : Tensor α [m, 1, k] := A.unsqueeze 1
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0]
    convert UnsqueezeDiv.eq.DivUnsqueeze A B 1 <;> simp
  let A_div : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ n)
  let A' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let C_r : Tensor α [k, n] := C.resize ⟨0, by grind⟩ k
  let CT : Tensor α [n, k] := C_rᵀ
  let C0 : Tensor α [1, n, k] := CT.unsqueeze 0
  let C' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, RepeatDiv.eq.DivRepeat A0 B ⟨1, by grind⟩ n]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  have hL : (A / B) @ C = (A_div * C').sum 2 := by
    simpa [A_div, A_div0, C', C0, CT, C_r] using Dot.eq.SumMul.of.Ge h (A / B) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, C', C0, CT, C_r] using Dot.eq.SumMul.of.Ge h A C
  rw [hL, hR, hA, MulDiv.eq.DivMul]
  exact SumDiv.eq.DivSum _ B 2

private lemma vector_matrix
  [Semifield α]
-- given
  (A : Tensor α [n])
  (C : Tensor α [k, d])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let K := n ⊔ k
  let A_div_r : Tensor α [K] := (A / B).resize ⟨0, by grind⟩ K
  let A_r : Tensor α [K] := A.resize ⟨0, by grind⟩ K
  have hr : A_div_r = A_r / B := by
    simp only [A_div_r, A_r]
    exact ResizeDiv.eq.DivResize A B ⟨0, by grind⟩ K
  let C_r : Tensor α [K, d] := C.resize ⟨0, by grind⟩ K
  let Adu0 : Tensor α [1, K] := A_div_r.unsqueeze 0
  let Au0 : Tensor α [1, K] := A_r.unsqueeze 0
  have hu0 : Adu0 = Au0 / B := by
    simp only [Adu0, Au0, hr]
    convert UnsqueezeDiv.eq.DivUnsqueeze A_r B 0 <;> simp
  let A_div0 : Tensor α [1, 1, K] := Adu0.unsqueeze 1
  let A0 : Tensor α [1, 1, K] := Au0.unsqueeze 1
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0, hu0]
    convert UnsqueezeDiv.eq.DivUnsqueeze Au0 B 1 <;> simp
  let A_div : Tensor α [1, d, K] :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ d)
  let A' : Tensor α [1, d, K] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ d)
  let CT : Tensor α [d, K] := C_rᵀ
  let C0 : Tensor α [1, d, K] := CT.unsqueeze 0
  let C' : Tensor α [1, d, K] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ 1)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, RepeatDiv.eq.DivRepeat A0 B ⟨1, by grind⟩ d]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  have hL : (A / B) @ C = ((A_div * C').sum 2).get ⟨0, by grind⟩ := by
    simpa [A_div, A_div0, Adu0, A_div_r, C', C0, CT, C_r, K] using
      Dot.eq.GetSumMul.resize (A / B) C
  have hR : A @ C = ((A' * C').sum 2).get ⟨0, by grind⟩ := by
    simpa [A', A0, Au0, A_r, C', C0, CT, C_r, K] using
      Dot.eq.GetSumMul.resize A C
  rw [hL, hR]
  have h_sum : (A_div * C').sum 2 = (A' * C').sum 2 / B := by
    rw [hA, MulDiv.eq.DivMul, SumDiv.eq.DivSum]
  rw [h_sum]
  exact GetDiv.eq.DivGet ((A' * C').sum 2) B ⟨0, by simp⟩


private lemma matrix_vector
  [Semifield α]
-- given
  (A : Tensor α [m, k])
  (C : Tensor α [d])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  rw [Dot.eq.SelectDot_Unsqueeze_1 (A / B) C]
  rw [Dot.eq.SelectDot_Unsqueeze_1 A C]
  have h : ((A / B) @ (C.unsqueeze 1)) = (A @ (C.unsqueeze 1)) / B := by
    if h : k = d then
      subst h
      exact matrix_matrix A (C.unsqueeze 1) B
    else if hlt : d < k then
      exact matrix_matrix_ge (le_of_lt hlt) A (C.unsqueeze 1) B
    else
      have hlt' : k < d := Nat.lt_of_le_of_ne (le_of_not_gt hlt) h
      exact matrix_matrix_lt hlt' A (C.unsqueeze 1) B
  have hsel := congrArg (fun t : Tensor α (matmul_shape [m, k] [d, 1]) => t.select ⟨1, by simp [matmul_shape]⟩ ⟨0, by simp [matmul_shape, broadcast_shape]⟩) h
  apply hsel.trans
  apply SelectDiv.eq.DivSelect


private lemma vector_vector_any
  [Semifield α]
-- given
  (A : Tensor α [n])
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  if h : n = n' then
    subst h
    exact vector_vector A C B
  else if hlt : n < n' then
    exact vector_vector_lt hlt A C B
  else
    have hgt : n > n' := Nat.lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)
    exact vector_vector_gt hgt A C B


private lemma matrix_matrix_any
  [Semifield α]
-- given
  (A : Tensor α [m, k])
  (C : Tensor α [k', n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  if h : k = k' then
    subst h
    exact matrix_matrix A C B
  else if hlt : k' < k then
    exact matrix_matrix_ge (le_of_lt hlt) A C B
  else
    have hlt' : k < k' := Nat.lt_of_le_of_ne (le_of_not_gt hlt) h
    exact matrix_matrix_lt hlt' A C B


/-- Batched matmul with equal batch and matching contract dims. -/
private lemma batch_matrix_matrix
  [Semifield α]
-- given
  (A : Tensor α (bz ++ [m, k]))
  (C : Tensor α (bz ++ [k, n]))
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let A_div0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [List.InsertIdxAppend.eq.Append_InsertIdx]))
      ((A / B).unsqueeze (bz.length + 1))
  let A0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [List.InsertIdxAppend.eq.Append_InsertIdx]))
      (A.unsqueeze (bz.length + 1))
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0]
    have hu := UnsqueezeDiv.eq.DivUnsqueeze A B (bz.length + 1)
    rw [hu]
    exact CastDiv.eq.DivCast.of.Eq (by simp [List.InsertIdxAppend.eq.Append_InsertIdx]) (A.unsqueeze (bz.length + 1)) B
  let A_div : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨bz.length + 1, by grind⟩ n)
  let A' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨bz.length + 1, by grind⟩ n)
  let CT : Tensor α (bz ++ [n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]
      simp [List.EqSwap_0'1])) Cᵀ
  let C0 : Tensor α (bz ++ [1, n, k]) :=
    cast (congrArg (Tensor α) (by simp [List.InsertIdxAppend.eq.Append_Cons]))
      (CT.unsqueeze bz.length)
  let C' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨bz.length, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, RepeatDiv.eq.DivRepeat A0 B ⟨bz.length + 1, by grind⟩ n]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  have hL : (A / B) @ C ≃ (A_div * C').sum (bz.length + 2) := by
    simpa [A_div, A_div0, C', C0, CT] using Dot.as.SumMul (A / B) C
  have hR : A @ C ≃ (A' * C').sum (bz.length + 2) := by
    simpa [A', A0, C', C0, CT] using Dot.as.SumMul A C
  have hsum : (A_div * C').sum (bz.length + 2) =
      (A' * C').sum (bz.length + 2) / B := by
    rw [hA, MulDiv.eq.DivMul, SumDiv.eq.DivSum]
  have hs : matmul_shape (bz ++ [m, k]) (bz ++ [k, n]) =
      (bz ++ [m, n, k]).eraseIdx (bz.length + 2) := hL.left
  have hL_eq : (A / B) @ C =
      cast (congrArg (Tensor α) hs.symm)
        ((A_div * C').sum (bz.length + 2)) := SEq.cast.comm hL
  have hR_eq : A @ C =
      cast (congrArg (Tensor α) hs.symm)
        ((A' * C').sum (bz.length + 2)) := SEq.cast.comm hR
  rw [hL_eq, hR_eq, hsum]
  apply CastDiv.eq.DivCast.of.Eq hs.symm


/-- `bmm` distributes over scalar division. -/
private lemma bmm_div
  [Semifield α]
-- given
  (A : Tensor α (bz ++ [m, k]))
  (C : Tensor α (bz ++ [k, n]))
  (B : Tensor α []) :
-- imply
  (A / B).bmm C = A.bmm C / B := by
-- proof
  let A_div0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [List.InsertIdxAppend.eq.Append_InsertIdx]))
      ((A / B).unsqueeze (bz.length + 1))
  let A0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [List.InsertIdxAppend.eq.Append_InsertIdx]))
      (A.unsqueeze (bz.length + 1))
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0]
    have hu := UnsqueezeDiv.eq.DivUnsqueeze A B (bz.length + 1)
    rw [hu]
    exact CastDiv.eq.DivCast.of.Eq (by simp [List.InsertIdxAppend.eq.Append_InsertIdx]) (A.unsqueeze (bz.length + 1)) B
  let A_div : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨bz.length + 1, by grind⟩ n)
  let A' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨bz.length + 1, by grind⟩ n)
  let CT : Tensor α (bz ++ [n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]
      simp [List.EqSwap_0'1])) Cᵀ
  let C0 : Tensor α (bz ++ [1, n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength (by simp)]
      simp))
      (CT.unsqueeze bz.length)
  let C' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨bz.length, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, RepeatDiv.eq.DivRepeat A0 B ⟨bz.length + 1, by grind⟩ n]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  have hsum : (A_div * C').sum (bz.length + 2) =
      (A' * C').sum (bz.length + 2) / B := by
    rw [hA, MulDiv.eq.DivMul, SumDiv.eq.DivSum]
  have hs :
      (bz ++ [m, n, k]).eraseIdx (bz.length + 2) = bz ++ [m, n] := by
    simp [List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength]
  have hL : (A / B).bmm C =
      cast (congrArg (Tensor α) hs)
        ((A_div * C').sum (bz.length + 2)) := by
    simp [Tensor.bmm, A_div, A_div0, C', C0, CT]
  have hR : A.bmm C =
      cast (congrArg (Tensor α) hs)
        ((A' * C').sum (bz.length + 2)) := by
    simp [Tensor.bmm, A', A0, C', C0, CT]
  rw [hL, hR, hsum]
  exact CastDiv.eq.DivCast.of.Eq hs _ B


/-- Equal-length-batch `matmul` distributes over scalar division. -/
private lemma matmul_div_eq_len
  [Semifield α]
  {s s' : List ℕ}
-- given
  (hlen : s.length = s'.length)
  (A : Tensor α (s ++ [m, t]))
  (C : Tensor α (s' ++ [t, k]))
  (B : Tensor α []) :
-- imply
  (A / B).matmul C hlen = A.matmul C hlen / B := by
-- proof
  induction s generalizing s' m t k with
  | nil =>
    match s' with
    | [] =>
      have hL := Matmul.as.Bmm (A / B) C
      have hR := Matmul.as.Bmm A C
      apply Bool.Eq.of.SEq
      exact hL.trans (Bool.SEq.of.Eq (bmm_div A C B)) |>.trans
        (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
    | _ :: _ =>
      simp at hlen
  | cons n s ih =>
    match s' with
    | [] =>
      simp at hlen
    | n' :: s' =>
      have hlen' : s.length = s'.length := by simpa using hlen
      have hcastA :
          ((n :: s) ++ [m, t]).set 0 (n ⊔ n') = (n ⊔ n' :: s) ++ [m, t] := by
        rw [List.SetAppend.eq.Append_Set.of.GtLength (by simp)]
        simp [List.Set_0.eq.Cons_Tail.of.GtLength_0]
      have hcastC :
          ((n' :: s') ++ [t, k]).set 0 (n ⊔ n') = (n ⊔ n' :: s') ++ [t, k] := by
        rw [List.SetAppend.eq.Append_Set.of.GtLength (by simp)]
        simp [List.Set_0.eq.Cons_Tail.of.GtLength_0]
      let Ar : Tensor α ((n ⊔ n' :: s) ++ [m, t]) :=
        cast (congrArg (Tensor α) hcastA) (A.resize ⟨0, by grind⟩ (n ⊔ n'))
      let Adr : Tensor α ((n ⊔ n' :: s) ++ [m, t]) :=
        cast (congrArg (Tensor α) hcastA) ((A / B).resize ⟨0, by grind⟩ (n ⊔ n'))
      let Cr : Tensor α ((n ⊔ n' :: s') ++ [t, k]) :=
        cast (congrArg (Tensor α) hcastC) (C.resize ⟨0, by grind⟩ (n ⊔ n'))
      have hAdr : Adr = Ar / B := by
        simp only [Adr, Ar]
        rw [ResizeDiv.eq.DivResize A B ⟨0, by grind⟩ (n ⊔ n')]
        exact CastDiv.eq.DivCast.of.Eq hcastA _ B
      have hL :=
        Matmul.as.MatmulResizeS.of.Length.GtLength_0 (s := n :: s) (s' := n' :: s')
          (by simp) hlen (A / B) C
      have hR :=
        Matmul.as.MatmulResizeS.of.Length.GtLength_0 (s := n :: s) (s' := n' :: s')
          (by simp) hlen A C
      have hmat : Adr.matmul Cr (by simpa using hlen') =
          Ar.matmul Cr (by simpa using hlen') / B := by
        rw [hAdr]
        have hshape :
            broadcast_shape (n ⊔ n' :: s) (n ⊔ n' :: s') ++ [m, k] =
              (n ⊔ n') :: (broadcast_shape s s' ++ [m, k]) := by
          simp [broadcast_shape]; split_ifs <;> simp_all
        let L : Tensor α ((n ⊔ n') :: (broadcast_shape s s' ++ [m, k])) :=
          cast (congrArg (Tensor α) hshape)
            ((Ar / B).matmul Cr (by simpa using hlen'))
        let R : Tensor α ((n ⊔ n') :: (broadcast_shape s s' ++ [m, k])) :=
          cast (congrArg (Tensor α) hshape)
            (Ar.matmul Cr (by simpa using hlen'))
        have hLR : L = R / B := by
          apply Tensor.Eq.of.All_EqGetS
          intro i
          rw [Tensor.GetDiv.eq.DivGet]
          apply Bool.Eq.of.SEq
          have hlenA : (n ⊔ n' :: s).length = (n ⊔ n' :: s').length := by
            simpa using hlen'
          have hgetL :=
            GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
              (s := n ⊔ n' :: s) (s' := n ⊔ n' :: s')
              (by simp) hlenA (by rfl) (Ar / B) Cr i
          have hgetR :=
            GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
              (s := n ⊔ n' :: s) (s' := n ⊔ n' :: s')
              (by simp) hlenA (by rfl) Ar Cr i
          have hCL :=
            GetCast.as.Get.of.Eq.GtLength_0.right.fin (by simp) hshape
              ((Ar / B).matmul Cr (by simpa using hlen')) i
          have hCR :=
            GetCast.as.Get.of.Eq.GtLength_0.right.fin (by simp) hshape
              (Ar.matmul Cr (by simpa using hlen')) i
          have hAi : (Ar / B)[i] = Ar[i] / B := Tensor.GetDiv.eq.DivGet Ar B i
          have ih' := ih hlen' (Ar[i]) (Cr[i])
          have hXA :
              (n ⊔ n' :: s) ++ [m, t] =
                ((n ⊔ n' :: s)[0] :: (n ⊔ n' :: s).tail) ++ [m, t] := by
            simp
          have hYA :
              (n ⊔ n' :: s') ++ [t, k] =
                ((n ⊔ n' :: s')[0] :: (n ⊔ n' :: s').tail) ++ [t, k] := by
            simp
          refine hCL.trans hgetL |>.trans ?_ |>.trans
            (Bool.SEqUFnS.of.SEq hgetR.symm
              (fun (t : Tensor α _) => (t / B : Tensor α _))) |>.trans
            (Bool.SEqUFnS.of.SEq hCR
              (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
          refine
            (SEqMatmulS.of.SEq.SEq (by simpa using hlen')
              ((GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hXA (Ar / B) i).trans (Bool.SEq.of.Eq hAi))
              (GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hYA Cr i)).trans
              (Bool.SEq.of.Eq ih')
        apply Bool.Eq.of.SEq
        refine (Bool.SEqCast.of.Eq hshape
            ((Ar / B).matmul Cr (by simpa using hlen'))).symm.trans ?_
        exact (Bool.SEq.of.Eq hLR).trans
          (Bool.SEqUFnS.of.SEq (Bool.SEqCast.of.Eq hshape
              (Ar.matmul Cr (by simpa using hlen')))
            (fun (t : Tensor α _) => (t / B : Tensor α _)))

      apply Bool.Eq.of.SEq
      refine hL.trans ?_
      have hmid := Bool.SEq.of.Eq hmat
      simpa [Adr, Ar, Cr] using
        hmid.trans (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Identical-batch `matmul` distributes over scalar division. -/
private lemma matmul_div
  [Semifield α]
  {s : List ℕ}
-- given
  (A : Tensor α (s ++ [m, t]))
  (C : Tensor α (s ++ [t, k]))
  (B : Tensor α []) :
-- imply
  (A / B).matmul C (by rfl) = A.matmul C (by rfl) / B :=
-- proof
  matmul_div_eq_len (by rfl) A C B


/-- Length-1 unequal-batch `matmul`. -/
private lemma matmul_div_len1
  [Semifield α]
-- given
  (A : Tensor α ([b] ++ [m, t]))
  (C : Tensor α ([b'] ++ [t, k]))
  (B : Tensor α []) :
-- imply
  (A / B).matmul C (by simp) = A.matmul C (by simp) / B :=
-- proof
  matmul_div_eq_len (by simp) A C B


/-- Identical-batch `tensordot` distributes over scalar division. -/
private lemma tensordot_div_same
  [Semifield α]
  {s : List ℕ}
-- given
  (A : Tensor α (s ++ [m, n]))
  (C : Tensor α (s ++ [n, k]))
  (B : Tensor α []) :
-- imply
  (A / B).tensordot C = A.tensordot C / B := by
-- proof
  have h1 := Tensordot.eq.Matmul.of.Length (by rfl) (A / B) C
  have h2 := Tensordot.eq.Matmul.of.Length (by rfl) A C
  rw [h1, h2]
  exact matmul_div A C B


/-- Both ranks ≥ 2 with equal batch prefixes. -/
private lemma both_ge_2
  [Semifield α]
-- given
  (hs : s.length ≥ 2)
  (hs' : s'.length ≥ 2)
  (hb : s.take (s.length - 2) = s'.take (s'.length - 2))
  (A : Tensor α s)
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' A C
  have hEd := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' (A / B) C
  apply Bool.Eq.of.SEq
  let batch := s.take (s.length - 2)
  let batch' := s'.take (s'.length - 2)
  let m := s[s.length - 2]
  let n := s[s.length - 1]
  let n' := s'[s'.length - 2]
  let k := s'[s'.length - 1]
  let K := n ⊔ n'
  let X0 : Tensor α (batch ++ [m, n]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
  let Xd0 : Tensor α (batch ++ [m, n]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
  have hXd0 : Xd0 = X0 / B :=
    CastDiv.eq.DivCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
  let X : Tensor α (batch ++ [m, K]) :=
    cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
  let Xd : Tensor α (batch ++ [m, K]) :=
    cast (by simp) (Xd0.resize ⟨batch.length + 1, by grind⟩ K)
  have hXd : Xd = X / B := by
    simp only [Xd, X, hXd0]
    rw [ResizeDiv.eq.DivResize X0 B ⟨batch.length + 1, by grind⟩ K]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  let Y0 : Tensor α (batch' ++ [n', k]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
  let Y' : Tensor α (batch' ++ [K, k]) :=
    cast (by simp) (Y0.resize ⟨batch'.length, by grind⟩ K)
  have hbY : batch' ++ [K, k] = batch ++ [K, k] := by
    simp only [batch, batch']; rw [hb]
  let Y : Tensor α (batch ++ [K, k]) :=
    cast (congrArg (Tensor α) hbY) Y'
  have hY : Y' ≃ Y := (Bool.SEqCast.of.Eq hbY Y').symm
  have htd : Xd.tensordot Y = X.tensordot Y / B := by
    rw [hXd]; exact tensordot_div_same X Y B
  have htd' : Xd.tensordot Y' = X.tensordot Y' / B := by
    apply Bool.Eq.of.SEq
    have h1 :=
      SEqTensordotS.of.SEq.SEq.Eq.Eq (by rfl) (by rfl) (by rfl : Xd ≃ Xd) hY
    have h2 :=
      SEqTensordotS.of.SEq.SEq.Eq.Eq (by rfl) (by rfl) (by rfl : X ≃ X) hY
    exact h1.trans (Bool.SEq.of.Eq htd) |>.trans
      (Bool.SEqUFnS.of.SEq h2.symm (fun (t : Tensor α _) => (t / B : Tensor α _)))
  have hL : (A / B).einsum C ≃ Xd.tensordot Y' := by
    refine hEd.trans ?_
    simp only [Xd, Xd0, Y', Y0, batch, batch', m, n, n', k, K]
    rfl
  have hR : A.einsum C ≃ X.tensordot Y' := by
    refine hE.trans ?_
    simp only [X, X0, Y', Y0, batch, batch', m, n, n', k, K]
    rfl
  exact hL.trans (Bool.SEq.of.Eq htd') |>.trans
    (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Rank-3 any leading/contract dims. -/
private lemma rank3_any
  [Semifield α]
-- given
  (A : Tensor α [b, m, k])
  (C : Tensor α [b', k', n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  if hb : b = b' then
    subst hb
    exact both_ge_2 (by simp) (by simp) (by simp) A C B
  else
    simp only [Dot.dot]
    have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 (by simp) (by simp) A C
    have hEd := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 (by simp) (by simp) (A / B) C
    let K := k ⊔ k'
    let X : Tensor α ([b] ++ [m, K]) :=
      cast (by simp) (A.resize ⟨2, by grind⟩ K)
    let Xd : Tensor α ([b] ++ [m, K]) :=
      cast (by simp) ((A / B).resize ⟨2, by grind⟩ K)
    let Y : Tensor α ([b'] ++ [K, n]) :=
      cast (by simp) (C.resize ⟨1, by grind⟩ K)
    have hXd : Xd = X / B := by
      simp only [Xd, X]
      rw [ResizeDiv.eq.DivResize A B ⟨2, by grind⟩ K]
      exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
    have htd : Xd.tensordot Y = X.tensordot Y / B := by
      have h1 := Tensordot.eq.Matmul.of.Length (by simp) Xd Y
      have h2 := Tensordot.eq.Matmul.of.Length (by simp) X Y
      rw [h1, h2, hXd]
      exact matmul_div_len1 (b := b) (b' := b') X Y B
    apply Bool.Eq.of.SEq
    have hL : (A / B).einsum C ≃ Xd.tensordot Y := by
      refine hEd.trans ?_
      simp only [Xd, Y, K]
      rfl
    have hR : A.einsum C ≃ X.tensordot Y := by
      refine hE.trans ?_
      simp only [X, Y, K]
      rfl
    exact hL.trans (Bool.SEq.of.Eq htd) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Vector @ rank ≥ 2. -/
private lemma vector_ge2
  [Semifield α]
-- given
  (hs' : s'.length ≥ 2)
  (A : Tensor α [n])
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  if h_eq : n = s'[s'.length - 2] then
    have hE := Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2 hs' h_eq A C
    have hEd := Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2 hs' h_eq (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let k := s'[s'.length - 1]
    let Y' : Tensor α (batch ++ [n, k]) :=
      cast (congrArg (Tensor α) (by
        simp only [batch, k]
        rw [h_eq]
        exact (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm)) C
    let X' := A.reshape (batch ++ [1, n]) (by simp)
    let Xd := (A / B).reshape (batch ++ [1, n]) (by simp)
    have hbmm : Xd.bmm Y' = X'.bmm Y' / B := by
      simp [Xd]
      rw [ReshapeDiv.eq.DivReshape.of.Dvd]
      apply bmm_div
    have hsel : (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ = (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]
      apply SelectDiv.eq.DivSelect
    have hL : (A / B).einsum C ≃ (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd, Y', batch, k]
      rfl
    have hR : A.einsum C ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', batch, k]
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else if hgt : n > s'[s'.length - 2] then
    have hE := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hs' hgt A C
    have hEd := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hs' hgt (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let n₀ := s'[s'.length - 2]
    let k' := s'[s'.length - 1]
    let Y0 : Tensor α (batch ++ [n₀, k']) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
    let Y' : Tensor α (batch ++ [n, k']) :=
      cast (by simp) (Y0.resize ⟨batch.length, by grind⟩ n)
    let X' := A.reshape (batch ++ [1, n]) (by simp)
    let Xd := (A / B).reshape (batch ++ [1, n]) (by simp)
    have hbmm : Xd.bmm Y' = X'.bmm Y' / B := by
      simp [Xd]
      rw [ReshapeDiv.eq.DivReshape.of.Dvd]
      apply bmm_div
    have hsel : (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ = (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]
      apply SelectDiv.eq.DivSelect
    have hL : (A / B).einsum C ≃ (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd, Y', Y0, batch, n₀, k']
      rfl
    have hR : A.einsum C ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', Y0, batch, n₀, k']
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else
    have hlt := Nat.lt_of_le_of_ne (le_of_not_gt hgt) h_eq
    have hE := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hs' hlt A C
    have hEd := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hs' hlt (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let n₀ := s'[s'.length - 2]
    let k' := s'[s'.length - 1]
    let Y' : Tensor α (batch ++ [n₀, k']) :=
      cast (congrArg (Tensor α) (by
        simp only [batch, n₀, k']
        exact (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm)) C
    let A_r : Tensor α [n₀] := cast (by simp) (A.resize ⟨0, by grind⟩ n₀)
    let Ad_r : Tensor α [n₀] := cast (by simp) ((A / B).resize ⟨0, by grind⟩ n₀)
    have hr : Ad_r = A_r / B := by
      simp only [Ad_r, A_r]
      rw [ResizeDiv.eq.DivResize A B ⟨0, by grind⟩ n₀]
      exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
    let X' := A_r.reshape (batch ++ [1, n₀]) (by simp)
    let Xd := Ad_r.reshape (batch ++ [1, n₀]) (by simp)
    have hx : Xd = X' / B := by
      simp only [Xd, X', hr]
      apply ReshapeDiv.eq.DivReshape.of.Dvd
    have hbmm : Xd.bmm Y' = X'.bmm Y' / B := by
      rw [hx]
      apply bmm_div X' Y' B
    have hsel : (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ = (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]
      apply SelectDiv.eq.DivSelect
    have hL : (A / B).einsum C ≃ (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd, Y', Ad_r, batch, n₀, k']
      rfl
    have hR : A.einsum C ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', A_r, batch, n₀, k']
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Rank ≥ 2 @ vector. -/
private lemma ge2_vector
  [Semifield α]
-- given
  (hs : s.length ≥ 2)
  (A : Tensor α s)
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  if h_eq : s[s.length - 1] = n' then
    have hE := Einsum.as.SelectBmm.of.EqGet_SubLength_1.GeLength_2 hs h_eq A C
    have hEd := Einsum.as.SelectBmm.of.EqGet_SubLength_1.GeLength_2 hs h_eq (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s.take (s.length - 2)
    let k := s[s.length - 2]
    let n := s[s.length - 1]
    let X0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Xd0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
    have hx0 : Xd0 = X0 / B :=
      CastDiv.eq.DivCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let Y' := C.reshape (batch ++ [n, 1]) (by simp_all [n])
    have hbmm : Xd0.bmm Y' = X0.bmm Y' / B := by
      rw [hx0]
      apply bmm_div X0 Y' B
    have hsel : (Xd0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ = (X0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]
      apply SelectDiv.eq.DivSelect
    have hL : (A / B).einsum C ≃ (Xd0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd0, Y', batch, k, n]
      rfl
    have hR : A.einsum C ≃
        (X0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X0, Y', batch, k, n]
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else if hge : s[s.length - 1] ≥ n' then
    have hE := Einsum.as.SelectBmm.of.GeGet_SubLength_1.GeLength_2 hs hge A C
    have hEd := Einsum.as.SelectBmm.of.GeGet_SubLength_1.GeLength_2 hs hge (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s.take (s.length - 2)
    let k := s[s.length - 2]
    let n := s[s.length - 1]
    let X0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Xd0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
    have hx0 : Xd0 = X0 / B :=
      CastDiv.eq.DivCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let Cr : Tensor α [n] := cast (by simp) (C.resize ⟨0, by grind⟩ n)
    let Y' := Cr.reshape (batch ++ [n, 1]) (by simp)
    have hbmm : Xd0.bmm Y' = X0.bmm Y' / B := by
      rw [hx0]
      apply bmm_div X0 Y' B
    have hsel : (Xd0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ = (X0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]
      apply SelectDiv.eq.DivSelect
    have hL : (A / B).einsum C ≃
        (Xd0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd0, Y', Cr, batch, k, n]
      rfl
    have hR : A.einsum C ≃
        (X0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X0, Y', Cr, batch, k, n]
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else
    have hlt : s[s.length - 1] < n' := Nat.lt_of_not_ge hge
    have hE := Einsum.as.SelectBmm.of.LtGet_SubLength_1.GeLength_2 hs hlt A C
    have hEd := Einsum.as.SelectBmm.of.LtGet_SubLength_1.GeLength_2 hs hlt (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s.take (s.length - 2)
    let k := s[s.length - 2]
    let n := s[s.length - 1]
    let X0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Xd0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
    have hx0 : Xd0 = X0 / B :=
      CastDiv.eq.DivCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let Xr : Tensor α (batch ++ [k, n']) :=
      cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ n')
    let Xdr : Tensor α (batch ++ [k, n']) :=
      cast (by simp) (Xd0.resize ⟨batch.length + 1, by grind⟩ n')
    have hxr : Xdr = Xr / B := by
      simp only [Xdr, Xr, hx0]
      rw [ResizeDiv.eq.DivResize X0 B ⟨batch.length + 1, by grind⟩ n']
      exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
    let Y' := C.reshape (batch ++ [n', 1]) (by simp)
    have hbmm : Xdr.bmm Y' = Xr.bmm Y' / B := by
      rw [hxr]
      apply bmm_div Xr Y'
    have hsel : (Xdr.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ = (Xr.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]
      apply SelectDiv.eq.DivSelect
    have hL : (A / B).einsum C ≃
        (Xdr.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xdr, Xd0, Y', batch, k, n]
      rfl
    have hR : A.einsum C ≃
        (Xr.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [Xr, X0, Y', batch, k, n]
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Arbitrary-batch `tensordot` distributes over scalar division. -/
private lemma tensordot_div
  [Semifield α]
  {s s' : List ℕ}
-- given
  (A : Tensor α (s ++ [m, n]))
  (C : Tensor α (s' ++ [n, k]))
  (B : Tensor α []) :
-- imply
  (A / B).tensordot C = A.tensordot C / B := by
-- proof
  if hlt : s.length < s'.length then
    have hL := Tensordot.as.Matmul.of.LtLengthS hlt (A / B) C
    have hR := Tensordot.as.Matmul.of.LtLengthS hlt A C
    let sR := s'.take (s'.length - s.length) ++ s ++ [m, n]
    have hdvd : (s ++ [m, n]).prod ∣ sR.prod := by grind
    have hmat := matmul_div_eq_len (by grind) (A.reshape sR hdvd) C B
    apply Bool.Eq.of.SEq
    refine hL.trans ?_
    -- `hL`/`hR` use `(by simp)` dvd proofs; align via convert/proof-irrel
    convert (Bool.SEq.of.Eq (by
      have hmat' : ((A / B).reshape sR hdvd).matmul C (by grind) = (A.reshape sR hdvd).matmul C (by grind) / B := by
        rwa [ReshapeDiv.eq.DivReshape.of.Dvd hdvd]
      exact hmat')).trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else if hgt : s.length > s'.length then
    have hge : s.length ≥ s'.length := Nat.le_of_lt hgt
    have hL := Tensordot.as.Matmul.of.GeLengthS hge (A / B) C
    have hR := Tensordot.as.Matmul.of.GeLengthS hge A C
    let sL := s.take (s.length - s'.length) ++ s' ++ [n, k]
    have hdvd : (s' ++ [n, k]).prod ∣ sL.prod := by
      have hsL : sL = s.take (s.length - s'.length) ++ (s' ++ [n, k]) := by grind
      rw [hsL]
      conv_rhs => rw [List.prod_append]
      exact Nat.dvd_mul_left _ _
    have hmat' :=
      matmul_div_eq_len (by grind) A (C.reshape sL hdvd) B
    apply Bool.Eq.of.SEq
    refine hL.trans ?_
    convert (Bool.SEq.of.Eq hmat').trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else
    have hlen := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
    have h1 := Tensordot.eq.Matmul.of.Length hlen (A / B) C
    have h2 := Tensordot.eq.Matmul.of.Length hlen A C
    rw [h1, h2]
    apply matmul_div_eq_len hlen


/-- Both ranks ≥ 2, possibly unequal batch prefixes. -/
private lemma both_ge_2_any
  [Semifield α]
-- given
  (hs : s.length ≥ 2)
  (hs' : s'.length ≥ 2)
  (A : Tensor α s)
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  if hb : s.take (s.length - 2) = s'.take (s'.length - 2) then
    apply both_ge_2 hs hs' hb
  else
    simp only [Dot.dot]
    have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' A C
    have hEd := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s.take (s.length - 2)
    let batch' := s'.take (s'.length - 2)
    let m := s[s.length - 2]
    let n := s[s.length - 1]
    let n' := s'[s'.length - 2]
    let k := s'[s'.length - 1]
    let K := n ⊔ n'
    let X0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Xd0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
    have hXd0 : Xd0 = X0 / B :=
      CastDiv.eq.DivCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let X : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
    let Xd : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (Xd0.resize ⟨batch.length + 1, by grind⟩ K)
    have hXd : Xd = X / B := by
      simp only [Xd, X, hXd0]
      rw [ResizeDiv.eq.DivResize X0 B ⟨batch.length + 1, by grind⟩ K]
      exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
    let Y0 : Tensor α (batch' ++ [n', k]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
    let Y' : Tensor α (batch' ++ [K, k]) :=
      cast (by simp) (Y0.resize ⟨batch'.length, by grind⟩ K)
    have htd : Xd.tensordot Y' = X.tensordot Y' / B := by
      rw [hXd]; exact tensordot_div X Y' B
    have hL : (A / B).einsum C ≃ Xd.tensordot Y' := by
      refine hEd.trans ?_
      simp only [Xd, Xd0, Y', Y0, batch, batch', m, n, n', k, K]
      rfl
    have hR : A.einsum C ≃ X.tensordot Y' := by
      refine hE.trans ?_
      simp only [X, X0, Y', Y0, batch, batch', m, n, n', k, K]
      rfl
    exact hL.trans (Bool.SEq.of.Eq htd) |>.trans (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Tensor-scalar form: division by a 0-dimensional tensor. -/
@[main]
private lemma main
  [Semifield α]
-- given
  (A : Tensor α s)
  (B : Tensor α [])
  (C : Tensor α s') :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  match s, s' with
  | [], _ =>
    grind [left_nil]
  | _ :: _, [] =>
    grind [right_nil]
  | [n], [n'] =>
    grind [vector_vector_any]
  | [n], [k, d] =>
    grind [vector_matrix]
  | [m, k], [d] =>
    grind [matrix_vector]
  | [m, k], [k', n] =>
    grind [matrix_matrix_any]
  | [b, m, k], [b', k', n] =>
    grind [rank3_any]
  | n :: rest, s' =>
    if hboth : (n :: rest).length ≥ 2 ∧ s'.length ≥ 2 then
      grind [both_ge_2_any]
    else if hvec : (n :: rest).length = 1 ∧ s'.length ≥ 2 then
      have hn : rest = [] := by aesop
      subst hn
      grind [vector_ge2]
    else if hleft : (n :: rest).length ≥ 2 ∧ s'.length = 1 then
      match s' with
      | [] =>
        grind
      | d :: t =>
        have ht : t = [] := by aesop
        subst ht
        grind [ge2_vector]
    else
      cases s' with
      | nil =>
        grind [right_nil]
      | cons _ t =>
        have ht : t = [] := by aesop
        subst ht
        have hn : rest = [] := by aesop
        subst hn
        grind [vector_vector_any]


-- created on 2026-08-11
-- updated on 2026-08-12
