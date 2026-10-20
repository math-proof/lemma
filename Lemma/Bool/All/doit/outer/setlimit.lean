import sympy.Basic


@[path]
private lemma main
  {a : ℤ}
  {f p : ℤ → ℤ → Prop} :
-- imply
  (∀ i ∈ ({a} : Set ℤ), ∀ j, f i j → p i j) ↔ ∀ j, f a j → p a j := by
-- proof
  simp


-- created on 2018-12-05
-- updated on 2026-10-17
