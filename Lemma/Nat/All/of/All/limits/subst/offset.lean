import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
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


-- created on 2018-12-10
