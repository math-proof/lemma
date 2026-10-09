import Lemma.Real.Anchors.Time.lt.TimeAdd1
import Lemma.Real.Anchors.TimeAdd1.eq.FindExistsLe


@[path]
private lemma main
  {α : ℕ → ℝ}
  {anc : Anchors α}
  {n : ℕ} :
-- imply
  anc.T n ≤ anc.β n := by
-- proof
  have h := Nat.find_spec (anc.exists_le n (anc.t n))
  rw [← (Real.Anchors.TimeAdd1.eq.FindExistsLe anc)] at h
  exact h


-- created on 2026-09-26