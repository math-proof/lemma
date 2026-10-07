import Mathlib.Topology.Order.MonotoneConvergence
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic




@[main]
private lemma main
  {a : ℕ → ℝ}
-- given
  (hge : ∀ n, a n ≤ a (n + 1))
  (hM : ∃ M, ∀ n, a n ≤ M) :
-- imply
  lim [n → ∞] a n = sSup (Set.range a) := by
-- proof
  have hmono : Monotone a := monotone_nat_of_le_succ hge
  obtain ⟨M, hM⟩ := hM
  have hbdd : BddAbove (Set.range a) :=
    ⟨M, fun z hz => by
      obtain ⟨n, rfl⟩ := hz
      exact hM n⟩
  have ht := tendsto_atTop_ciSup hmono hbdd
  rw [← sSup_range] at ht
  exact ht


-- created on 2020-05-20
-- updated on 2023-11-11
