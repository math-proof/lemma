import stdlib.Slice


@[main]
private lemma main
-- given
  (a b : ℤ)
  (n : ℕ) :
-- imply
  (⟨a, b, 0⟩ : Slice).length n = 0 := by
-- proof
  simp [Slice.length]


-- created on 2026-08-09
