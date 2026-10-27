import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : ι → Prop} [DecidablePred p]
  {A B g : ι → Set α} :
-- imply
  (⋂ i, ((if p i then A i else B i) ∪ g i)) =
    (⋂ i ∈ {i | p i}, (A i ∪ g i)) ∩ (⋂ i ∈ {i | ¬ p i}, (B i ∪ g i)) := by
-- proof
  ext x
  simp
  grind


-- created on 2021-01-27
-- updated on 2026-10-26
