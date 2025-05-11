import sympy.tensor.tensor
import Lemma.Basic


@[main]
private lemma main
  [Mul α]
  {a b : Tensor α s} :
-- imply
  a * b = ⟨a.data.val.zipWith HMul.hMul b.data.val, by simp [Tensor.data]⟩ := by
-- proof
  rfl


-- created on 2025-05-02
