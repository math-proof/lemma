import Instance.Data.Tensor.Tensor


@[path]
private lemma main
  {X : Tensor α s}
  {i : ℕ}
-- given
  (h : X.length > i) :
-- imply
  X[i] = X.get ⟨i, h⟩ := by
-- proof
  rfl


-- created on 2025-07-10
-- updated on 2026-11-20
