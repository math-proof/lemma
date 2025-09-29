import Lemma.Set.CupIn_Ico.eq.Cup_UfnSub
open Set


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (n : ℕ) :
-- imply
  ⋃ k ∈ Ico (-n : ℤ) (0 : ℤ), Ioc (k : R) (k + 1 : R) = Ioc (-n : R) (0 : R) := by
-- proof
  rw [CupIn_Ico.eq.Cup_UfnSub (d := (n : ℤ))]
  sorry


-- created on 2025-09-29
