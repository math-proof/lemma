import sympy.Basic


@[main]
private lemma main
  [Field α]
  [NeZero c]
  [NeZero d]
  {a b x : α}
-- given
  (h₀ : a = d * x)
  (h₁ : b = c * x) :
-- imply
  a / d = b / c := calc
-- proof
  a / d = d * x / d := by rw [h₀]
  _ = x := by simp [NeZero.ne d]
  _ = c * x / c := by simp [NeZero.ne c]
  _ = b / c := by rw [h₁]


-- created on 2024-07-01
-- updated on 2025-10-01
