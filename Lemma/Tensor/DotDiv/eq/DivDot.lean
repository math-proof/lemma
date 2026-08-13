import Lemma.Tensor.Div.eq.Div_GetData_0
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SelectDot_Unsqueeze_1
import Lemma.Tensor.DotDiv.eq.DivDot.of.GeLength_2
import Lemma.Tensor.DotDiv.eq.DivDot.of.GeLength_2.GeLength_2
import Lemma.Tensor.Einsum.eq.MulGetData_0
import Lemma.Tensor.Einsum.eq.SumMulDataS.of.Gt
import Lemma.Tensor.Einsum.eq.SumMulDataS.of.Lt
import Lemma.Tensor.MulDiv.eq.DivMul
import Lemma.Tensor.RepeatDiv.eq.DivRepeat
import Lemma.Tensor.ResizeDiv.eq.DivResize
import Lemma.Tensor.SelectDiv.eq.DivSelect
import Lemma.Tensor.SumDiv.eq.DivSum
import Lemma.Tensor.UnsqueezeDiv.eq.DivUnsqueeze
open Tensor


private lemma nil
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


private lemma vector
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
    repeat rw [Dot.eq.SumMul__0]
    rw [MulDiv.eq.DivMul]
    apply SumDiv.eq.DivSum
  else if hlt : n < n' then
    simp only [Dot.dot]
    repeat rw [Einsum.eq.SumMulDataS.of.Lt hlt]
    rw [ResizeDiv.eq.DivResize]
    rw [CastDiv.eq.DivCast.of.Eq (by simp)]
    rw [MulDiv.eq.DivMul]
    apply SumDiv.eq.DivSum
  else
    have hgt := Nat.lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)
    simp only [Dot.dot]
    repeat rw [Einsum.eq.SumMulDataS.of.Gt hgt]
    erw [MulDiv.eq.DivMul]
    apply SumDiv.eq.DivSum


@[main]
private lemma matrix
  [Semifield α]
-- given
  (A : Tensor α [m, k])
  (C : Tensor α [k', n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let K := k ⊔ k'
  let A_div_r : Tensor α [m, K] := (A / B).resize ⟨1, by grind⟩ K
  let A_r : Tensor α [m, K] := A.resize ⟨1, by grind⟩ K
  have hr : A_div_r = A_r / B := by
    simp only [A_div_r, A_r]
    exact ResizeDiv.eq.DivResize A B ⟨1, by grind⟩ K
  let A_div0 : Tensor α [m, 1, K] := A_div_r.unsqueeze 1
  let A0 : Tensor α [m, 1, K] := A_r.unsqueeze 1
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0, hr]
    convert UnsqueezeDiv.eq.DivUnsqueeze A_r B 1 <;> simp
  let A_div : Tensor α [m, n, K] :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ n)
  let A' : Tensor α [m, n, K] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let C_r : Tensor α [K, n] := C.resize ⟨0, by grind⟩ K
  let CT : Tensor α [n, K] := C_rᵀ
  let C0 : Tensor α [1, n, K] := CT.unsqueeze 0
  let C' : Tensor α [m, n, K] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, RepeatDiv.eq.DivRepeat A0 B ⟨1, by grind⟩ n]
    apply CastDiv.eq.DivCast.of.Eq
    simp
  have hL : (A / B) @ C = (A_div * C').sum 2 := by
    simpa [A_div, A_div0, A_div_r, C', C0, CT, C_r, K] using Dot.eq.SumMul.resize (A / B) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, A_r, C', C0, CT, C_r, K] using Dot.eq.SumMul.resize A C
  rw [hL, hR, hA, MulDiv.eq.DivMul]
  apply SumDiv.eq.DivSum


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
    simp only [Dot.dot]
    repeat rw [Einsum.eq.MulGetData_0]
    simp [HDiv.hDiv]
    refine (MulDiv.eq.DivMul.left (A.data[0]) B.data[0] C).trans ?_
    rfl
  | _ :: _, [] =>
    grind [nil]
  | [n], [n'] =>
    grind [vector]
  | [n], [k, d] =>
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
    let A_div : Tensor α [1, d, K] := cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ d)
    let A' : Tensor α [1, d, K] := cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ d)
    let CT : Tensor α [d, K] := C_rᵀ
    let C0 : Tensor α [1, d, K] := CT.unsqueeze 0
    let C' : Tensor α [1, d, K] := cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ 1)
    have hA : A_div = A' / B := by
      simp only [A_div, A']
      rw [h0, RepeatDiv.eq.DivRepeat A0 B ⟨1, by grind⟩ d]
      apply CastDiv.eq.DivCast.of.Eq (by simp)
    have hL : (A / B) @ C = ((A_div * C').sum 2).get ⟨0, by grind⟩ := by
      simpa [A_div, A_div0, Adu0, A_div_r, C', C0, CT, C_r, K] using Dot.eq.GetSumMul.resize (A / B) C
    have hR : A @ C = ((A' * C').sum 2).get ⟨0, by grind⟩ := by
      simpa [A', A0, Au0, A_r, C', C0, CT, C_r, K] using Dot.eq.GetSumMul.resize A C
    rw [hL, hR]
    rw [hA, MulDiv.eq.DivMul, SumDiv.eq.DivSum]
    exact GetDiv.eq.DivGet ((A' * C').sum 2) B ⟨0, by simp⟩
  | [m, k], [d] =>
    repeat rw [Dot.eq.SelectDot_Unsqueeze_1]
    have h : ((A / B) @ (C.unsqueeze 1)) = (A @ (C.unsqueeze 1)) / B := by
      apply matrix
    have hsel := congrArg (fun t : Tensor α (matmul_shape [m, k] [d, 1]) => t.select ⟨1, by simp [matmul_shape]⟩ ⟨0, by simp [matmul_shape, broadcast_shape]⟩) h
    apply hsel.trans
    apply SelectDiv.eq.DivSelect
  | [m, k], [k', n] =>
    apply matrix
  | [b, m, k], [b', k', n] =>
    apply DotDiv.eq.DivDot.of.GeLength_2.GeLength_2 (by simp) (by simp)
  | n :: rest, s' =>
    if hboth : (n :: rest).length ≥ 2 ∧ s'.length ≥ 2 then
      apply DotDiv.eq.DivDot.of.GeLength_2.GeLength_2 hboth.1 hboth.2
    else if hvec : (n :: rest).length = 1 ∧ s'.length ≥ 2 then
      have hn : rest = [] := by aesop
      subst hn
      apply DotDiv.eq.DivDot.of.GeLength_2 hvec.2
    else if hleft : (n :: rest).length ≥ 2 ∧ s'.length = 1 then
      match s' with
      | [] =>
        grind
      | d :: t =>
        have ht : t = [] := by aesop
        subst ht
        apply DotDiv.eq.DivDot.of.GeLength_2.left hleft.1
    else
      cases s' with
      | nil =>
        grind [nil]
      | cons _ t =>
        have ht : t = [] := by aesop
        subst ht
        have hn : rest = [] := by aesop
        subst hn
        grind [vector]


-- created on 2026-08-11
-- updated on 2026-08-13
