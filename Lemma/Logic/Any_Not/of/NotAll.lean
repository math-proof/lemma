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
  -- Use classical reasoning to handle the negation and existence
  classical
  -- Apply the principle of excluded middle to derive the existence of an element not satisfying f
  by_contra! h'
  -- Obtain a contradiction by combining the original hypothesis with the derived universal statement
  exact h (fun i hi => by simpa using h' i hi)


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
