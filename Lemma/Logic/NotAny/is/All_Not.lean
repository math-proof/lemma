import Lemma.Logic.All.is.NotAny_Not
open Logic


@[main, comm, mp, mpr]
private lemma fin
-- given
  (s : Finset ι)
  (p : ι → Prop) :
-- imply
  ¬(∃ i ∈ s, p i) ↔ ∀ i ∈ s, ¬(p i) := by
-- proof
  rw [All.is.NotAny_Not]
  simp


@[main, comm, mp, mpr]
private lemma main
-- given
  (p : α → Prop) :
-- imply
  (¬∃ x : α, p x) ↔ ∀ x : α, ¬p x := by
-- proof
  rw [All.is.NotAny_Not]
  simp


-- created on 2024-07-01
