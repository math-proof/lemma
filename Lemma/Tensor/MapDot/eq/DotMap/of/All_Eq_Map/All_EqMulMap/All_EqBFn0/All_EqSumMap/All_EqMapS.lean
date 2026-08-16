import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SelectDot_Unsqueeze_1
import Lemma.Tensor.DotBFn.eq.BFnDot.of.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.DotBFn.eq.BFnDot.of.GeLength_2.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.MapDot.eq.DotMap.of.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.MapDot.eq.DotMap.of.All_EqMulMap
import Lemma.Tensor.Einsum.eq.MulGetData_0
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.MapCast.as.MapBFn.of.Eq
import Lemma.Tensor.RepeatBFn.eq.BFnRepeat
import Lemma.Tensor.ResizeBFn.eq.BFnResize
import Lemma.Tensor.SelectBFn.eq.BFnSelect
import Lemma.Tensor.UnsqueezeBFn.eq.BFnUnsqueeze
open Tensor


/-- `dot` commutes with a pointwise scalar binary operator `f`. -/
@[main, comm]
private lemma main
  [Mul α] [Add α] [Zero α]
  {f : α → α → α}
-- given
  (h_mul : ∀ {s : List ℕ} (X C : Tensor α s) (B : Tensor α []), X.map (f · B.data[0]) * C = (X * C).map (f · B.data[0]))
  (h_sum : ∀ {s : List ℕ} (X : Tensor α s) (B : Tensor α []) (dim : ℕ), (X.map (f · B.data[0])).sum dim = (X.sum dim).map (f · B.data[0]))
  (h0 : ∀ b : α, f 0 b = 0)
  (h_right : ∀ {s : List ℕ} (X : Tensor α s) (c b : α), X.map (f · b) * c = (X * c).map (f · b))
  (h_left : ∀ {s : List ℕ} (a b : α) (C : Tensor α s), f a b * C = (a * C).map (f · b))
  (A : Tensor α s)
  (B : Tensor α [])
  (C : Tensor α s') :
-- imply
  (A @ C).map (f · B.data[0]) = (A.map (f · B.data[0])) @ C := by
-- proof
  apply Eq.symm
  match s, s' with
  | [], _ =>
    simp only [Dot.dot]
    repeat rw [Einsum.eq.MulGetData_0]
    have hdata : (A.map (f · B.data[0])).data[0] = f A.data[0] B.data[0] := by
      simp [Tensor.map]
      rfl
    rw [hdata]
    apply h_left
  | _ :: _, [] =>
    apply DotMap.eq.MapDot.of.All_EqMulMap h_right
  | [n], [n'] =>
    apply DotMap.eq.MapDot.of.All_EqBFn0.All_EqSumMap.All_EqMapS.vector h_mul h_sum h0
  | [n], [k, d] =>
    let F {s} (X : Tensor α s) : Tensor α s := X.map (f · B.data[0])
    let K := n ⊔ k
    let A_f_r : Tensor α [K] := (F A).resize ⟨0, by grind⟩ K
    let A_r : Tensor α [K] := A.resize ⟨0, by grind⟩ K
    have hr : A_f_r = F A_r := by
      simp only [A_f_r, A_r, F]
      exact ResizeBFn.eq.BFnResize h0 A B ⟨0, by grind⟩ K
    let Af0 : Tensor α [1, K] := A_f_r.unsqueeze 0
    let Au0 : Tensor α [1, K] := A_r.unsqueeze 0
    have hu0 : Af0 = F Au0 := by
      simp only [Af0, Au0, hr]
      apply UnsqueezeBFn.eq.BFnUnsqueeze
    let A_f0 : Tensor α [1, 1, K] := Af0.unsqueeze 1
    let A0 : Tensor α [1, 1, K] := Au0.unsqueeze 1
    have hu : A_f0 = F A0 := by
      simp only [A_f0, A0, hu0]
      apply UnsqueezeBFn.eq.BFnUnsqueeze
    let A_f : Tensor α [1, d, K] := cast (congrArg (Tensor α) (by simp)) (A_f0.repeat ⟨1, by grind⟩ d)
    let A' : Tensor α [1, d, K] := cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ d)
    let C_r : Tensor α [K, d] := C.resize ⟨0, by grind⟩ K
    let CT : Tensor α [d, K] := C_rᵀ
    let C0 : Tensor α [1, d, K] := CT.unsqueeze 0
    let C' : Tensor α [1, d, K] := cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ 1)
    have hA : A_f = F A' := by
      simp only [A_f, A']
      rw [hu, RepeatBFn.eq.BFnRepeat f A0 B ⟨1, by grind⟩ d]
      apply Cast_MapBFn.eq.MapCast.of.Eq
      simp
    have hL : (F A) @ C = ((A_f * C').sum 2).get ⟨0, by grind⟩ := by
      simpa [F, A_f, A_f0, Af0, A_f_r, C', C0, CT, C_r, K] using Dot.eq.GetSumMul.resize (F A) C
    have hR : A @ C = ((A' * C').sum 2).get ⟨0, by grind⟩ := by
      simpa [A', A0, Au0, A_r, C', C0, CT, C_r, K] using Dot.eq.GetSumMul.resize A C
    rw [hL, hR, hA, h_mul, h_sum]
    apply GetMap.eq.MapGet (i := ⟨0, by simp [Tensor.length]⟩)
  | [m, k], [d] =>
    repeat rw [Dot.eq.SelectDot_Unsqueeze_1]
    have h := DotMap.eq.MapDot.of.All_EqBFn0.All_EqSumMap.All_EqMapS.matrix h_mul h_sum h0 A (C.unsqueeze 1) B
    have hsel := congrArg (fun t : Tensor α (matmul_shape [m, k] [d, 1]) => t.select ⟨1, by simp [matmul_shape]⟩ ⟨0, by simp [matmul_shape, broadcast_shape]⟩) h
    apply hsel.trans
    apply SelectBFn.eq.BFnSelect
  | [m, k], [k', n] =>
    apply DotMap.eq.MapDot.of.All_EqBFn0.All_EqSumMap.All_EqMapS.matrix h_mul h_sum h0
  | [b, m, k], [b', k', n] =>
    apply DotBFn.eq.BFnDot.of.GeLength_2.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS h_mul h_sum h0 (by simp) (by simp)
  | n :: rest, s' =>
    if hboth : (n :: rest).length ≥ 2 ∧ s'.length ≥ 2 then
      apply DotBFn.eq.BFnDot.of.GeLength_2.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS h_mul h_sum h0 hboth.1 hboth.2
    else if hvec : (n :: rest).length = 1 ∧ s'.length ≥ 2 then
      have hn : rest = [] := by aesop
      subst hn
      apply DotBFn.eq.BFnDot.of.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS h_mul h_sum h0 hvec.2
    else if hleft : (n :: rest).length ≥ 2 ∧ s'.length = 1 then
      match s' with
      | [] =>
        grind
      | d :: t =>
        have ht : t = [] := by aesop
        subst ht
        apply DotBFn.eq.BFnDot.of.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS.left h_mul h_sum h0 hleft.1
    else
      cases s' with
      | nil =>
        apply DotMap.eq.MapDot.of.All_EqMulMap h_right
      | cons _ t =>
        have ht : t = [] := by aesop
        subst ht
        have hn : rest = [] := by aesop
        subst hn
        apply DotMap.eq.MapDot.of.All_EqBFn0.All_EqSumMap.All_EqMapS.vector h_mul h_sum h0


-- created on 2026-08-15
-- updated on 2026-08-17
