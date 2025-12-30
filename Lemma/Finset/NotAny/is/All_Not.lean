import Lemma.Bool.All.is.NotAny_Not
open Bool


@[main, comm, mp, mpr]
private lemma main
-- given
  (s : Finset ι)
  (p : ι → Prop) :
-- imply
  ¬(∃ i ∈ s, p i) ↔ ∀ i ∈ s, ¬(p i) := by
-- proof
  rw [All.is.NotAny_Not]
  simp


-- created on 2025-12-30
