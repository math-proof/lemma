import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : ι → Set α}
-- given
  (h₀ : ∀ i, g i ⊆ f i) :
-- imply
  (⋃ i, g i) ⊆ ⋃ i, f i :=
-- proof
  Set.iUnion_mono h₀


-- created on 2021-01-15
-- updated on 2026-10-26
