import sympy.Basic


@[path]
private lemma main
  {f : ℤ → Prop}
  {a b d : ℤ} :
-- imply
  (∀ n ∈ Set.Ico a b, f n) ↔
    ∀ n ∈ Set.Ico (a - d) (b - d), f (n + d) := by
-- proof
  constructor
  ·
    intro h n hn
    apply h (n + d)
    simp only [Set.mem_Ico] at hn ⊢
    omega
  ·
    intro h n hn
    have h' := h (n - d) (by simp only [Set.mem_Ico] at hn ⊢; omega)
    rwa [sub_add_cancel] at h'


-- created on 2026-10-11
