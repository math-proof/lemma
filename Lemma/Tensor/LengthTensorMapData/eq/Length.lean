import sympy.tensor.tensor
import sympy.Basic


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (f : α → α):
-- imply
  (⟨X.data.map f⟩ : Tensor α s).length = X.length := by
-- proof
  cases s <;>
  ·
    simp [Tensor.length]


-- created on 2025-10-08
