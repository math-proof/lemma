import sympy.Basic


@[main]
private lemma main
  {f : ι → Prop}
  {s : Finset ι}
-- given
  (h : ∀ i ∈ s, f i) :
-- imply
  ¬∃ i ∈ s, ¬(f i) := by
-- proof
  by_contra! h'
  let ⟨i, hi, hni⟩ := h'
  exact absurd (h i hi) hni


-- created on 2025-12-30
