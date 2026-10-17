import sympy.Basic


@[path]
private lemma main
  {f g : ι → Set α}
-- given
  (h₀ : ∀ i, g i ⊆ f i) :
-- imply
  (⋃ i, g i) ⊆ ⋃ i, f i :=
-- proof
  Set.iUnion_mono h₀


-- created on 2026-10-11
-- updated on 2026-10-17
