import Lemma.Anchors.Time.lt.TimeAdd1
open Finset Filter


@[main]
private lemma main
  {α : ℕ → ℝ}
  {anc : Anchors α}
  {n : ℕ} :
-- imply
  anc.β n ≤ anc.T n + α (anc.t (n + 1) - 1) := by
-- proof
  have h₁ : anc.t n < anc.t (n + 1) := Anchors.Time.lt.TimeAdd1
  have hlt : ¬anc.le n (anc.t n) (anc.t (n + 1) - 1) :=
    Nat.find_min (anc.exists_le n (anc.t n)) (by rw [← anc.t_succ]; omega)
  simp only [Anchors.le, not_le] at hlt
  have e : anc.β n = ∑ i ∈ Ico (anc.t n) (anc.t (n + 1) - 1), α i + α (anc.t (n + 1) - 1) := by
    unfold Anchors.β
    conv_lhs => rw [show anc.t (n + 1) = anc.t (n + 1) - 1 + 1 by omega]
    rw [sum_Ico_succ_top (by omega)]
  linarith


-- created on 2026-09-26