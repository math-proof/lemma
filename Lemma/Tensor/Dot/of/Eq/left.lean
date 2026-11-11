import Instance.LinearAlgebra.Matrix.Matmul
import Instance.Data.Vector.Basic.Dot


@[path]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (t : Tensor α [n])
  (X Y : Tensor α [n, n])
  (h : X = Y) :
-- imply
  t ⬝ᵥ X = t ⬝ᵥ Y := by
-- proof
  exact congrArg (fun M : Tensor α [n, n] => t ⬝ᵥ M) h


-- created on 2020-08-16
