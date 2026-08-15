import Lemma.Tensor.CastMul.eq.MulCast.of.Eq
import Lemma.Tensor.Mul.eq.Mul_GetData_0
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SelectDot_Unsqueeze_1
import Lemma.Tensor.DotMul.eq.MulDot.of.GeLength_2
import Lemma.Tensor.DotMul.eq.MulDot.of.GeLength_2.GeLength_2
import Lemma.Tensor.Einsum.eq.MulGetData_0
import Lemma.Tensor.Einsum.eq.SumMulDataS.of.Gt
import Lemma.Tensor.Einsum.eq.SumMulDataS.of.Lt
import Lemma.Tensor.GetMul.eq.MulGet
import Lemma.Tensor.MulMul
import Lemma.Tensor.RepeatMul.eq.MulRepeat
import Lemma.Tensor.ResizeMul.eq.MulResize
import Lemma.Tensor.SelectMul.eq.MulSelect
import Lemma.Tensor.SumMul.eq.MulSum
import Lemma.Tensor.UnsqueezeMul.eq.MulUnsqueeze
open Tensor
set_option maxHeartbeats 1000000


private lemma nil
  [CommSemiring α]
-- given
  (A : Tensor α (n :: s))
  (B : Tensor α [])
  (C : Tensor α []) :
-- imply
  (A * B) @ C = A @ C * B := by
-- proof
  simp only [Dot.dot]
  unfold einsum
  have h_mul : (A * B) * C.data[0] = (A * C.data[0]) * B := by
    rw [Mul.eq.Mul_GetData_0 A B, Mul.eq.Mul_GetData_0 (A * C.data[0]) B]
    exact MulMul.comm.right A C.data[0] B.data[0]
  refine Eq.trans (congrArg (cast (by simp [matmul_shape])) h_mul) ?_
  apply CastMul.eq.MulCast.of.Eq
  simp [matmul_shape]


private lemma vector
  [CommSemiring α]
-- given
  (A : Tensor α [n])
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A * B) @ C = A @ C * B := by
-- proof
  if h : n = n' then
    subst h
    repeat rw [Dot.eq.SumMul__0]
    rw [MulMul.comm]
    apply SumMul.eq.MulSum
  else if hlt : n < n' then
    simp only [Dot.dot]
    repeat rw [Einsum.eq.SumMulDataS.of.Lt hlt]
    rw [ResizeMul.eq.MulResize]
    rw [CastMul.eq.MulCast.of.Eq (by simp)]
    rw [MulMul.comm]
    apply SumMul.eq.MulSum
  else
    have hgt := Nat.lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)
    simp only [Dot.dot]
    repeat rw [Einsum.eq.SumMulDataS.of.Gt hgt]
    erw [MulMul.comm]
    apply SumMul.eq.MulSum


@[main]
private lemma matrix
  [CommSemiring α]
-- given
  (A : Tensor α [m, k])
  (C : Tensor α [k', n])
  (B : Tensor α []) :
-- imply
  (A * B) @ C = A @ C * B := by
-- proof
  let K := k ⊔ k'
  let A_mul_r : Tensor α [m, K] := (A * B).resize ⟨1, by grind⟩ K
  let A_r : Tensor α [m, K] := A.resize ⟨1, by grind⟩ K
  have hr : A_mul_r = A_r * B := by
    simp only [A_mul_r, A_r]
    exact ResizeMul.eq.MulResize A B ⟨1, by grind⟩ K
  let A_mul0 : Tensor α [m, 1, K] := A_mul_r.unsqueeze 1
  let A0 : Tensor α [m, 1, K] := A_r.unsqueeze 1
  have h0 : A_mul0 = A0 * B := by
    simp only [A_mul0, A0, hr]
    convert UnsqueezeMul.eq.MulUnsqueeze A_r B 1 <;> simp
  let A_mul : Tensor α [m, n, K] :=
    cast (congrArg (Tensor α) (by simp)) (A_mul0.repeat ⟨1, by grind⟩ n)
  let A' : Tensor α [m, n, K] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let C_r : Tensor α [K, n] := C.resize ⟨0, by grind⟩ K
  let CT : Tensor α [n, K] := C_rᵀ
  let C0 : Tensor α [1, n, K] := CT.unsqueeze 0
  let C' : Tensor α [m, n, K] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hA : A_mul = A' * B := by
    simp only [A_mul, A']
    rw [h0, RepeatMul.eq.MulRepeat A0 B ⟨1, by grind⟩ n]
    apply CastMul.eq.MulCast.of.Eq
    simp
  have hL : (A * B) @ C = (A_mul * C').sum 2 := by
    simpa [A_mul, A_mul0, A_mul_r, C', C0, CT, C_r, K] using Dot.eq.SumMul.resize (A * B) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, A_r, C', C0, CT, C_r, K] using Dot.eq.SumMul.resize A C
  rw [hL, hR, hA, MulMul.comm]
  apply SumMul.eq.MulSum


@[main]
private lemma main
  [CommSemiring α]
-- given
  (A : Tensor α s)
  (B : Tensor α [])
  (C : Tensor α s') :
-- imply
  (A * B) @ C = A @ C * B := by
-- proof
  match s, s' with
  | [], _ =>
    simp only [Dot.dot]
    repeat rw [Einsum.eq.MulGetData_0]
    simp [HMul.hMul]
    refine (MulMul.comm.left (A.data[0]) B.data[0] C).trans ?_
    rfl
  | _ :: _, [] =>
    grind [nil]
  | [n], [n'] =>
    grind [vector]
  | [n], [k, d] =>
    let K := n ⊔ k
    let A_mul_r : Tensor α [K] := (A * B).resize ⟨0, by grind⟩ K
    let A_r : Tensor α [K] := A.resize ⟨0, by grind⟩ K
    have hr : A_mul_r = A_r * B := by
      simp only [A_mul_r, A_r]
      exact ResizeMul.eq.MulResize A B ⟨0, by grind⟩ K
    let C_r : Tensor α [K, d] := C.resize ⟨0, by grind⟩ K
    let Amu0 : Tensor α [1, K] := A_mul_r.unsqueeze 0
    let Au0 : Tensor α [1, K] := A_r.unsqueeze 0
    have hu0 : Amu0 = Au0 * B := by
      simp only [Amu0, Au0, hr]
      convert UnsqueezeMul.eq.MulUnsqueeze A_r B 0 <;> simp
    let A_mul0 : Tensor α [1, 1, K] := Amu0.unsqueeze 1
    let A0 : Tensor α [1, 1, K] := Au0.unsqueeze 1
    have h0 : A_mul0 = A0 * B := by
      simp only [A_mul0, A0, hu0]
      convert UnsqueezeMul.eq.MulUnsqueeze Au0 B 1 <;> simp
    let A_mul : Tensor α [1, d, K] := cast (congrArg (Tensor α) (by simp)) (A_mul0.repeat ⟨1, by grind⟩ d)
    let A' : Tensor α [1, d, K] := cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ d)
    let CT : Tensor α [d, K] := C_rᵀ
    let C0 : Tensor α [1, d, K] := CT.unsqueeze 0
    let C' : Tensor α [1, d, K] := cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ 1)
    have hA : A_mul = A' * B := by
      simp only [A_mul, A']
      rw [h0, RepeatMul.eq.MulRepeat A0 B ⟨1, by grind⟩ d]
      apply CastMul.eq.MulCast.of.Eq (by simp)
    have hL : (A * B) @ C = ((A_mul * C').sum 2).get ⟨0, by grind⟩ := by
      simpa [A_mul, A_mul0, Amu0, A_mul_r, C', C0, CT, C_r, K] using Dot.eq.GetSumMul.resize (A * B) C
    have hR : A @ C = ((A' * C').sum 2).get ⟨0, by grind⟩ := by
      simpa [A', A0, Au0, A_r, C', C0, CT, C_r, K] using Dot.eq.GetSumMul.resize A C
    rw [hL, hR]
    rw [hA, MulMul.comm, SumMul.eq.MulSum]
    exact GetMul.eq.MulGet ((A' * C').sum 2) B ⟨0, by simp⟩
  | [m, k], [d] =>
    repeat rw [Dot.eq.SelectDot_Unsqueeze_1]
    have h : ((A * B) @ (C.unsqueeze 1)) = (A @ (C.unsqueeze 1)) * B := by
      apply matrix
    have hsel := congrArg (fun t : Tensor α (matmul_shape [m, k] [d, 1]) => t.select ⟨1, by simp [matmul_shape]⟩ ⟨0, by simp [matmul_shape, broadcast_shape]⟩) h
    apply hsel.trans
    apply SelectMul.eq.MulSelect
  | [m, k], [k', n] =>
    apply matrix
  | [b, m, k], [b', k', n] =>
    apply DotMul.eq.MulDot.of.GeLength_2.GeLength_2 (by simp) (by simp)
  | n :: rest, s' =>
    if hboth : (n :: rest).length ≥ 2 ∧ s'.length ≥ 2 then
      apply DotMul.eq.MulDot.of.GeLength_2.GeLength_2 hboth.1 hboth.2
    else if hvec : (n :: rest).length = 1 ∧ s'.length ≥ 2 then
      have hn : rest = [] := by aesop
      subst hn
      apply DotMul.eq.MulDot.of.GeLength_2 hvec.2
    else if hleft : (n :: rest).length ≥ 2 ∧ s'.length = 1 then
      match s' with
      | [] =>
        grind
      | d :: t =>
        have ht : t = [] := by aesop
        subst ht
        apply DotMul.eq.MulDot.of.GeLength_2.left hleft.1
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


-- created on 2026-08-15
