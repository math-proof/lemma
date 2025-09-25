import Lemma.Basic


@[main]
private lemma fin
  {f : ι → Prop}
  {s : Finset ι}
-- given
  (h : ¬∀ i ∈ s, f i) :
-- imply
  ∃ i ∈ s, ¬(f i) := by
-- proof
  by_contra! h'
  contradiction


@[main]
private lemma main
  {p : α → Prop}
-- given
  (h : ¬∀ x : α, p x) :
-- imply
  ∃ x : α, ¬p x := by
-- proof
  push_neg at h
  exact h


-- created on 2024-07-01
