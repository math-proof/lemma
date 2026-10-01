import sympy.Basic


@[main]
private lemma main
  {f : ℤ → Prop}
  {a b : ℤ}
-- given
  (h : ∀ i ∈ Set.Ico a b, f i) :
-- imply
  ∀ i ∈ Set.Ico (1 - b) (1 - a), f (-i) := by
-- proof
  intro i hi
  apply h
  simp only [Set.mem_Ico] at hi ⊢
  omega


@[main]
private lemma given
  {f : ℤ → Prop}
  {a b : ℤ}
-- given
  (h : ∀ i ∈ Set.Ico (1 - b) (1 - a), f (-i)) :
-- imply
  ∀ i ∈ Set.Ico a b, f i := by
-- proof
  intro i hi
  have h' := h (-i) (by simp only [Set.mem_Ico] at hi ⊢; omega)
  rwa [neg_neg] at h'


-- created on 2026-09-27
