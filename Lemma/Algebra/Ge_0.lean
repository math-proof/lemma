import Lemma.Basic


@[main]
private lemma nat
-- given
  (n : ℕ) :
-- imply
  n ≥ 0 := by
-- proof
  simp


@[main]
private lemma main
  [Semiring R] [PartialOrder R] [IsOrderedRing R]
  {n : ℕ} :
-- imply
  (n : R) ≥ 0 := by
-- proof
  simp



-- created on 2025-04-12
-- updated on 2025-06-01
