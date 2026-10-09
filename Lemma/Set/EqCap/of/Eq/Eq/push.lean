import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  {a b : ℤ}
  {f g : ℤ → Set α}
-- given
  (h₀ : a < b)
  (h₁ : g b = f b)
  (h₂ : (Finset.Ico a b).inf g = (Finset.Ico a b).inf f) :
-- imply
  (Finset.Ico a (b + 1)).inf g = (Finset.Ico a (b + 1)).inf f := by
-- proof
  have hrange : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  simp only [hrange, Finset.inf_insert, h₂, h₁]


-- created on 2021-01-10
