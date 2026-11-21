import Instance.Data.Tensor.Defs.Part2


@[path]
private lemma main
  [Mul α]
  {A B X Y : Tensor α s}
-- given
  (h₀ : A = B)
  (h₁ : X = Y) :
-- imply
  A * X = B * Y := by
-- proof
  rw [h₀, h₁]


-- created on 2025-12-03
-- updated on 2026-11-20
