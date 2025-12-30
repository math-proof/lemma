import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [DecidableEq ι]
-- given
  (x : α)
  (s : Finset ι)
  (f : ι → Finset α) :
-- imply
  x ∈ ⋃ i ∈ s, f i ↔ ∃ i ∈ s, x ∈ f i := by
-- proof
  simp


-- created on 2025-12-30
