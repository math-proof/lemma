import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : ι → Prop} [DecidablePred p]
  {f g : ι → Set α} :
-- imply
  (⋂ i, if p i then f i else g i) =
    (⋂ i ∈ {i | p i}, f i) ∩ (⋂ i ∈ {i | ¬ p i}, g i) := by
-- proof
  ext x
  simp
  grind


-- created on 2021-01-26
-- updated on 2026-10-26
