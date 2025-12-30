import sympy.Basic


@[main, comm]
private lemma main
-- given
  (s : Finset ι)
  (p : ι → Prop) :
-- imply
  (¬∀ x : s, p x) ↔ ∃ x : s, ¬p x := by
-- proof
  push_neg
  rfl


-- created on 2025-12-30
