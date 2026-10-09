import sympy.Basic


@[path]
private lemma limits.subst.offset.given
  {f : ℤ → Prop}
  {a b d : ℤ}
-- given
  (h : ∀ n ∈ Set.Ico (a - d) (b - d), f (n + d)) :
-- imply
  ∀ n ∈ Set.Ico a b, f n := by
-- proof
  intro n hn
  have h' := h (n - d) (by simp only [Set.mem_Ico] at hn ⊢; omega)
  rwa [sub_add_cancel] at h'


@[path]
private lemma limits.subst.reverse.given
  {f : ℤ → Prop}
  {a b c : ℤ}
-- given
  (h : ∀ n ∈ Set.Ico (c + 1 - b) (c + 1 - a), f (c - n)) :
-- imply
  ∀ n ∈ Set.Ico a b, f n := by
-- proof
  intro n hn
  have h' := h (c - n) (by simp only [Set.mem_Ico] at hn ⊢; omega)
  rwa [sub_sub_cancel] at h'


-- created on 2026-09-27
