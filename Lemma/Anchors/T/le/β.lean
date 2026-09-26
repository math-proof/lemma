import Lemma.Anchors.Time.lt.TimeAdd1
open Finset Filter


@[main]
private lemma main
  {α : ℕ → ℝ}
  {anc : Anchors α}
  {n : ℕ} :
-- imply
  anc.T n ≤ anc.β n := by
-- proof
  have h := Nat.find_spec (anc.exists_le n (anc.t n))
  rw [← anc.t_succ] at h
  exact h


-- created on 2026-09-26