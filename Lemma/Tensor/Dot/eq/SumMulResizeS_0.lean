import Instance.LinearAlgebra.Matrix.Matmul
import Def.Data.Tensor.Sum
import Instance.Data.Vector.Basic.Dot
@[path]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [n])
  (B : Tensor α [n']) :
-- imply
  let n := n ⊔ n'
  let A' : Tensor α [n] := A.resize ⟨0, by grind⟩ n
  let B' : Tensor α [n] := B.resize ⟨0, by grind⟩ n
  A ⬝ᵥ B = (A' * B').sum 0 := by
-- proof
  simp [Dot.dot]
  unfold Tensor.einsum
  simp
  rfl


-- created on 2026-08-13
