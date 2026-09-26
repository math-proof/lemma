import Lemma.Anchors.StrictMonoTime
import Lemma.Anchors.T.le.β
import Lemma.Anchors.β.le.AddT_GetSub1TimeAdd1
import Lemma.Finset.SumIco_SumIco.eq.SumIco.of.Monotone.Le
open Finset Filter


@[main]
private lemma main
  {α : ℕ → ℝ}
  {anc : Anchors α}
  {m : ℕ} :
-- imply
  ∑ k ∈ range m, anc.T k ≤ ∑ k ∈ range (anc.t m), α k := by
-- proof
  induction m with
  | zero => simp [anc.t_zero]
  | succ m ih =>
    have h := Anchors.T.le.β (anc := anc) (n := m)
    unfold Anchors.β at h
    rw [sum_range_succ, range_eq_Ico, range_eq_Ico,
      ← sum_Ico_consecutive _ (Nat.zero_le (anc.t m)) Anchors.Time.lt.TimeAdd1.le]
    rw [range_eq_Ico, range_eq_Ico] at ih
    linarith


-- created on 2026-09-26