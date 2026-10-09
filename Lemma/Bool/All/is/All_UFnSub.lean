import sympy.Basic


@[path]
private lemma main
  {f : ℤ → Prop}
  {a b c : ℤ} :
-- imply
  (∀ i ∈ Set.Ico a b, f i) ↔
    ∀ i ∈ Set.Ico (c + 1 - b) (c + 1 - a), f (c - i) := by
-- proof
  constructor
  · intro h i hi
    simp only [Set.mem_Ico] at hi ⊢
    exact h (c - i) ⟨by omega, by omega⟩
  · intro h i hi
    simp only [Set.mem_Ico] at hi ⊢
    have h' := h (c - i) ⟨by omega, by omega⟩
    rwa [sub_sub_cancel] at h'


-- created on 2018-06-20
