/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PottsCriticalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.IsingFK.BetacPc.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
open Real Set


namespace StatMech

namespace FK

theorem fkgq_fkTheta_eq_zero_of_lt_pc
    {d : ℕ} {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hpc : p < fkPc d q) :
    fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) = 0 := by
  have hne : (fkSubcriticalSet d q).Nonempty := by
    rcases (fkSubcriticalSet d q).eq_empty_or_nonempty with hempty | hne
    · exfalso
      rw [fkPc, hempty, Real.sSup_empty] at hpc
      linarith
    · exact hne
  obtain ⟨p', hp'mem, hpp'⟩ := exists_lt_of_lt_csSup hne hpc
  obtain ⟨hp'0, hp'1, _hq', htheta'⟩ := hp'mem
  have hmono :
      fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) ≤
        fkTheta d hp'0 hp'1 (zero_lt_one.trans_le hq) (q := q) :=
    fkgq_fkTheta_monotone_in_p hp hp1 hp'0 hp'1 hpp'.le hq
  refine le_antisymm ?_ (fkTheta_nonneg d hp hp1 (zero_lt_one.trans_le hq) (q := q))
  exact hmono.trans_eq htheta'

end FK

namespace IsingFK


theorem betaC_eq_of_strict_transition (mStar : ℝ → ℝ) (t : ℝ)
    (ht : 0 < t)
    (hbelow : ∀ beta, 0 < beta → beta < t → mStar beta = 0)
    (habove : ∀ beta, t < beta → 0 < mStar beta) :
    betaC mStar = t := by
  let S : Set ℝ := {beta | 0 < beta ∧ mStar beta = 0}
  have hsub : Set.Ioo (0 : ℝ) t ⊆ S := by
    rintro beta ⟨hbeta0, hbetat⟩
    exact ⟨hbeta0, hbelow beta hbeta0 hbetat⟩
  have hSnonempty : S.Nonempty := by
    refine ⟨t / 2, ?_⟩
    have ht2 : 0 < t / 2 := by linarith
    have ht2t : t / 2 < t := by linarith
    exact ⟨ht2, hbelow (t / 2) ht2 ht2t⟩
  have hSle : ∀ beta ∈ S, beta ≤ t := by
    rintro beta ⟨hbeta0, hzero⟩
    by_contra hnot
    have hpos := habove beta (lt_of_not_ge hnot)
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  have hSbdd : BddAbove S := ⟨t, hSle⟩
  unfold betaC
  change sSup S = t
  apply le_antisymm
  · exact csSup_le hSnonempty hSle
  · rw [← csSup_Ioo ht]
    exact csSup_le_csSup hSbdd (Set.nonempty_Ioo.mpr ht) hsub


end IsingFK
end StatMech
