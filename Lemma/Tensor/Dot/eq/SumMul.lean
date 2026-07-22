import Lemma.Tensor.Dot.eq.Bmm
open Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, k])
  (B : Tensor α [k, n]) :
-- imply
  let A' : Tensor α [m, 1, k] := A.unsqueeze 1
  let A' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (A'.repeat ⟨1, by grind⟩ n)
  let B' : Tensor α [n, k] := Bᵀ
  let B' : Tensor α [1, n, k] := B'.unsqueeze 0
  let B' : Tensor α [m, n, k] := cast (congrArg (Tensor α) (by simp)) (B'.repeat ⟨0, by grind⟩ m)
  A @ B = (A' * B').sum 2 := by
-- proof
  rw [Dot.eq.Bmm]
  simp [Tensor.bmm]
  congr 1


-- created on 2026-07-10
-- updated on 2026-07-21
