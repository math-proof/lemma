import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A : Set ι}
  {s : ι → Set κ}
  {f : κ → ι → Prop} :
-- imply
  (∃ j ∈ A, ∃ i ∈ s j, f i j) ↔ ∃ i ∈ A, ∃ j ∈ s i, f j i :=
-- proof
  Iff.rfl




-- created on 2026-09-27
-- updated on 2026-11-24
