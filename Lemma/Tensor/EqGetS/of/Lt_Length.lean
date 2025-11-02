import sympy.tensor.tensor
import sympy.Basic


@[main]
private lemma main
  {X : Tensor α s}
  {i : ℕ}
-- given
  (h : i < X.length) :
-- imply
  X[i] = X.get ⟨i, h⟩ := by
-- proof
  simp [GetElem.getElem]


-- created on 2025-07-10
