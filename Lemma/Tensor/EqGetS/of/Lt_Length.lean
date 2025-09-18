import sympy.tensor.tensor
import Lemma.Basic


@[main]
private lemma main
  {v : Tensor α s}
  {i : ℕ}
-- given
  (h : i < v.length) :
-- imply
  v[i] = v.get ⟨i, h⟩ := by
-- proof
  simp [GetElem.getElem]


-- created on 2025-07-10
