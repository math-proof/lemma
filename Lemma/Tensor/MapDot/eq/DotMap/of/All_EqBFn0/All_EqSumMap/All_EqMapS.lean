import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Einsum.eq.SumMulDataS
import Lemma.Tensor.MapCast.as.MapBFn.of.Eq
import Lemma.Tensor.RepeatBFn.eq.BFnRepeat
import Lemma.Tensor.ResizeBFn.eq.BFnResize
import Lemma.Tensor.UnsqueezeBFn.eq.BFnUnsqueeze
open Tensor


/-- `dot` of two vectors commutes with a pointwise scalar binary operator `f`. -/
@[main, comm]
private lemma vector
  [Mul α] [Add α] [Zero α]
  {f : α → α → α}
-- given
  (h_mul : ∀ {s : List ℕ} (X C : Tensor α s) (B : Tensor α []), X.map (f · B.data[0]) * C = (X * C).map (f · B.data[0]))
  (h_sum : ∀ {s : List ℕ} (X : Tensor α s) (B : Tensor α []) (dim : ℕ), (X.map (f · B.data[0])).sum dim = (X.sum dim).map (f · B.data[0]))
  (h0 : ∀ b : α, f 0 b = 0)
  (A : Tensor α [n])
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A @ C).map (f · B.data[0]) = (A.map (f · B.data[0])) @ C := by
-- proof
  apply Eq.symm
  let K := n ⊔ n'
  let A' : Tensor α [K] := A.resize ⟨0, by grind⟩ K
  let C' : Tensor α [K] := C.resize ⟨0, by grind⟩ K
  let Af' : Tensor α [K] := (A.map (f · B.data[0])).resize ⟨0, by grind⟩ K
  have hr : Af' = A'.map (f · B.data[0]) := by
    simp only [Af', A']
    exact ResizeBFn.eq.BFnResize h0 A B ⟨0, by grind⟩ K
  have hL : (A.map (f · B.data[0])) @ C = (Af' * C').sum := by
    simp only [Dot.dot]
    simpa [Af', C', K] using Einsum.eq.SumMulDataS.resize (A.map (f · B.data[0])) C
  have hR : A @ C = (A' * C').sum := by
    simp only [Dot.dot]
    simpa [A', C', K] using Einsum.eq.SumMulDataS.resize A C
  rw [hL, hR, hr, h_mul]
  apply h_sum


/-- `dot` of two matrices commutes with a pointwise scalar binary operator `f`. -/
@[main, comm]
private lemma matrix
  [Mul α] [Add α] [Zero α]
  {f : α → α → α}
-- given
  (h_mul : ∀ {s : List ℕ} (X C : Tensor α s) (B : Tensor α []), X.map (f · B.data[0]) * C = (X * C).map (f · B.data[0]))
  (h_sum : ∀ {s : List ℕ} (X : Tensor α s) (B : Tensor α []) (dim : ℕ), (X.map (f · B.data[0])).sum dim = (X.sum dim).map (f · B.data[0]))
  (h0 : ∀ b : α, f 0 b = 0)
  (A : Tensor α [m, k])
  (C : Tensor α [k', n])
  (B : Tensor α []) :
-- imply
  (A @ C).map (f · B.data[0]) = (A.map (f · B.data[0])) @ C := by
-- proof
  apply Eq.symm
  let F {s} (X : Tensor α s) : Tensor α s := X.map (f · B.data[0])
  let K := k ⊔ k'
  let A_f_r : Tensor α [m, K] := (F A).resize ⟨1, by grind⟩ K
  let A_r : Tensor α [m, K] := A.resize ⟨1, by grind⟩ K
  have hr : A_f_r = F A_r := by
    simp only [A_f_r, A_r, F]
    exact ResizeBFn.eq.BFnResize h0 A B ⟨1, by grind⟩ K
  let A_f0 : Tensor α [m, 1, K] := A_f_r.unsqueeze 1
  let A0 : Tensor α [m, 1, K] := A_r.unsqueeze 1
  have hu : A_f0 = F A0 := by
    simp only [A_f0, A0, hr]
    apply UnsqueezeBFn.eq.BFnUnsqueeze
  let A_f : Tensor α [m, n, K] :=
    cast (congrArg (Tensor α) (by simp)) (A_f0.repeat ⟨1, by grind⟩ n)
  let A' : Tensor α [m, n, K] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let C_r : Tensor α [K, n] := C.resize ⟨0, by grind⟩ K
  let CT : Tensor α [n, K] := C_rᵀ
  let C0 : Tensor α [1, n, K] := CT.unsqueeze 0
  let C' : Tensor α [m, n, K] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hA : A_f = F A' := by
    simp only [A_f, A']
    rw [hu, RepeatBFn.eq.BFnRepeat f A0 B ⟨1, by grind⟩ n]
    apply Cast_MapBFn.eq.MapCast.of.Eq
    simp
  have hL : (F A) @ C = (A_f * C').sum 2 := by
    simpa [F, A_f, A_f0, A_f_r, C', C0, CT, C_r, K] using Dot.eq.SumMul.resize (F A) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, A_r, C', C0, CT, C_r, K] using Dot.eq.SumMul.resize A C
  rw [hL, hR, hA, h_mul, h_sum]
  rfl


-- created on 2026-08-15
-- updated on 2026-08-17
