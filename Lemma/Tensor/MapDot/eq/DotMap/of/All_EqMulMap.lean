import Lemma.Tensor.MapCast.as.MapBFn.of.Eq
import sympy.tensor.tensor
open Tensor


/-- `dot` with a 0-d right factor commutes with a pointwise scalar binary operator `f`. -/
@[main, comm]
private lemma main
  [Mul α] [Add α] [Zero α]
  {f : α → α → α}
-- given
  (h_mul : ∀ {s : List ℕ} (X : Tensor α s) (c b : α), X.map (f · b) * c = (X * c).map (f · b))
  (A : Tensor α (n :: s))
  (B : Tensor α [])
  (C : Tensor α []) :
-- imply
  (A @ C).map (f · B.data[0]) = (A.map (f · B.data[0])) @ C := by
-- proof
  apply Eq.symm
  simp only [Dot.dot]
  unfold einsum
  have h : (A.map (f · B.data[0])) * C.data[0] = (A * C.data[0]).map (f · B.data[0]) :=
    h_mul A C.data[0] B.data[0]
  refine Eq.trans (congrArg (cast (by simp [matmul_shape])) h) ?_
  apply Cast_MapBFn.eq.MapCast.of.Eq
  simp [matmul_shape]


-- created on 2026-08-15
-- updated on 2026-08-17
