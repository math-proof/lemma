import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  {a b : ℤ}
  {f g : ℤ → Set α}
-- given
  (h₀ : a < b)
  (h₁ : g (a - 1) = f (a - 1))
  (h₂ : (Finset.Ico a b).sup g = (Finset.Ico a b).sup f) :
-- imply
  (Finset.Ico (a - 1) b).sup g = (Finset.Ico (a - 1) b).sup f := by
-- proof
  have hrange : Finset.Ico (a - 1) b = insert (a - 1) (Finset.Ico a b) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  simp only [hrange, Finset.sup_insert, h₂, h₁]


-- created on 2021-03-29
