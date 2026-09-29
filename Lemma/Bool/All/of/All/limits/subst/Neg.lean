import sympy.Basic


@[main]
private lemma real
  {f : ℝ → Prop}
  {a b c : ℝ}
-- given
  (h : ∀ x ∈ Set.Ioc a b, f x) :
-- imply
  ∀ x ∈ Set.Ico (c - b) (c - a), f (c - x) := by
-- proof
  intro x hx
  apply h
  simp only [Set.mem_Ico, Set.mem_Ioc] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]


-- created on 2026-09-27
