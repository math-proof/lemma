import Lemma.Real.Eq_AddMulPiFloorDiv_Pi.of.EqCos_0
open Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : cos x = 0) :
-- imply
  ∃ n : ℤ, x = π * n + π / 2 := by
-- proof
  refine ⟨⌊x / π⌋, ?_⟩
  exact Eq_AddMulPiFloorDiv_Pi.of.EqCos_0 h


-- created on 2018-06-24
