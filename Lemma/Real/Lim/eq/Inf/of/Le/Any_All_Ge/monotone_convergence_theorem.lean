import Mathlib.Topology.Order.MonotoneConvergence
import Def.Analysis.Real.Limits.Part4
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a : ℕ → ℝ}
-- given
  (hle : ∀ n, a (n + 1) ≤ a n)
  (hM : ∃ M, ∀ n, M ≤ a n) :
-- imply
  lim [n → ∞] a n = sInf (Set.range a) := by
-- proof
  have hanti : Antitone a := antitone_nat_of_succ_le hle
  obtain ⟨M, hM⟩ := hM
  have hbdd : BddBelow (Set.range a) :=
    ⟨M, fun z hz => by
      obtain ⟨n, rfl⟩ := hz
      exact hM n⟩
  have ht := tendsto_atTop_ciInf hanti hbdd
  rw [← sInf_range] at ht
  exact ht


-- created on 2020-06-24
