import sympy.Basic


@[path]
private lemma main
  {m n : ℕ}
  {p : ℕ → ℕ → Prop} :
-- imply
  (∀ j ∈ Finset.range n, ∀ i ∈ Finset.range m, p i j) ↔
    ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range n, p i j := by
-- proof
  constructor
  ·
    intro h i hi j hj
    apply h j hj i hi
  ·
    intro h j hj i hi
    apply h i hi j hj


-- created on 2018-12-05
-- updated on 2026-10-17
