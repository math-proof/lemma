import Lemma.Real.Anchors.StrictMonoTime
import Lemma.Real.Anchors.T.le.β
import Lemma.Real.Anchors.β.le.AddT_GetSub1TimeAdd1
import Lemma.Finset.SumIco_SumIco.eq.SumIco.of.Monotone.Le
import Lemma.Real.Anchors.Time0.eq.Zero
open Finset


@[main]
private lemma main
  {α : ℕ → ℝ}
  {anc : Anchors α} :
-- imply
  RobbinsMonro anc.β := by
-- proof
  have hpos : ∀ n, 0 < anc.β n := fun n =>
    sum_pos (fun i _ => anc.hα.pos i) (nonempty_Ico.2 Real.Anchors.Time.lt.TimeAdd1)
  have hf : StrictMono fun n => anc.t (n + 1) - 1 := strictMono_nat_of_lt_succ fun n => by
    have h₁ : anc.t (n + 1) < anc.t (n + 1 + 1) := Real.Anchors.Time.lt.TimeAdd1
    have h₂ : anc.t n < anc.t (n + 1) := Real.Anchors.Time.lt.TimeAdd1
    omega
  refine ⟨hpos, ?_, ?_⟩
  · refine (anc.hα.sum.comp (Real.Anchors.StrictMonoTime (anc := anc)).tendsto_atTop).congr fun n => ?_
    have h := Finset.SumIco_SumIco.eq.SumIco.of.Monotone.Le (Nat.zero_le n) (Real.Anchors.StrictMonoTime (anc := anc)).monotone α
    simp only [Function.comp, range_eq_Ico, (Real.Anchors.Time0.eq.Zero anc)] at h ⊢
    exact h.symm
  · exact Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => (pow_le_pow_left₀ (hpos n).le Real.Anchors.β.le.AddT_GetSub1TimeAdd1 2).trans add_sq_le)
      ((anc.hT.sqsum.add (anc.hα.sqsum.comp_injective hf.injective)).mul_left 2)


-- created on 2026-09-26