import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPhaseEndpoint
open MeasureTheory StatMech StatMech.Onsager


/--
[ons_signedLoopPhaseWeight_eq_tanh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma ons_signedLoopPhaseWeight_eq_tanh_eq
  {beta : Real}
-- given
  (hbeta : beta ≤ ons_betaC) :
-- imply
  ons_signedLoopPhaseWeight beta = Real.tanh beta := by
-- proof
  apply StatMech.Onsager.ons_signedLoopPhaseWeight_eq_tanh hbeta

/--
[ons_signedLoopPhaseWeight_eq_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma ons_signedLoopPhaseWeight_eq_exp_eq
  {beta : Real}
-- given
  (hbeta : ons_betaC < beta) :
-- imply
  ons_signedLoopPhaseWeight beta = Real.exp (-2 * beta) := by
-- proof
  apply StatMech.Onsager.ons_signedLoopPhaseWeight_eq_exp hbeta

/--
[ons_signedLoopPhaseWeight_lt_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma ons_signedLoopPhaseWeight_lt_critical_eq
  {beta : Real}
-- given
  (hbeta : beta ≠ ons_betaC) :
-- imply
  ons_signedLoopPhaseWeight beta < ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.ons_signedLoopPhaseWeight_lt_critical hbeta

/--
[ons_signedLoopPhaseWeight_selfDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma ons_signedLoopPhaseWeight_selfDual_eq :
-- imply
  ons_signedLoopPhaseWeight ons_betaC = ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.ons_signedLoopPhaseWeight_selfDual

/--
[ons_signedLoopPhaseWeight_eq_critical_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma ons_signedLoopPhaseWeight_eq_critical_iff_eq
  {beta : Real} :
-- imply
  ons_signedLoopPhaseWeight beta = ons_signedLoopCriticalWeight ↔ beta = ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_signedLoopPhaseWeight_eq_critical_iff beta

/--
[isingBetaC_two_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma isingBetaC_two_pos_eq :
-- imply
  0 < StatMech.Ising.betaC 2 := by
-- proof
  apply StatMech.Onsager.isingBetaC_two_pos

/--
[freeState_eq_plusState_of_magnetization_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma freeState_eq_plusState_of_magnetization_eq_zero_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta)
  (hmag : magnetization d beta = 0) :
-- imply
  (freeState d beta 0 : Measure (ConfigSpace (Site d))) = (plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Onsager.freeState_eq_plusState_of_magnetization_eq_zero beta hbeta hmag

/--
[freeState_twoPoint_exponential_below_isingBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma freeState_twoPoint_exponential_below_isingBetaC_eq
  {beta : Real}
-- given
  (hbeta0 : 0 < beta)
  (hbeta : beta < StatMech.Ising.betaC 2) :
-- imply
  ∃ c > 0, ∀ z : Site 2, (∫ config, spin config (Percolation.origin 2) * spin config z ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) ≤ Real.exp (-c * (l1dist 2 (Percolation.origin 2) z : Real)) := by
-- proof
  apply StatMech.Onsager.freeState_twoPoint_exponential_below_isingBetaC hbeta0 hbeta

/--
[plusState_twoPoint_longRange_above_isingBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma plusState_twoPoint_longRange_above_isingBetaC_eq
  {beta : Real}
-- given
  (hbeta : StatMech.Ising.betaC 2 < beta) :
-- imply
  ∃ c > 0, ∀ z : Site 2, c ≤ plusCorr 2 beta (Percolation.origin 2) z := by
-- proof
  apply StatMech.Onsager.plusState_twoPoint_longRange_above_isingBetaC hbeta

/--
[isingBetaC_two_eq_ons_betaC_of_dual_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma isingBetaC_two_eq_ons_betaC_of_dual_fixed_eq
-- given
  (hfixed : dualTemp (StatMech.Ising.betaC 2) = StatMech.Ising.betaC 2) :
-- imply
  StatMech.Ising.betaC 2 = ons_betaC := by
-- proof
  apply StatMech.Onsager.isingBetaC_two_eq_ons_betaC_of_dual_fixed hfixed

/--
[signedLoop_physical_phase_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean)
-/
@[path]
private lemma signedLoop_physical_phase_threshold_eq
-- given
  (hfixed : dualTemp (StatMech.Ising.betaC 2) = StatMech.Ising.betaC 2) :
-- imply
  (∀ {beta : Real}, 0 < beta → beta < ons_betaC → ∃ c > 0, ∀ z : Site 2, (∫ config, spin config (Percolation.origin 2) * spin config z ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) ≤ Real.exp (-c * (l1dist 2 (Percolation.origin 2) z : Real))) ∧ (∀ {beta : Real}, ons_betaC < beta → ∃ c > 0, ∀ z : Site 2, c ≤ plusCorr 2 beta (Percolation.origin 2) z) := by
-- proof
  apply StatMech.Onsager.signedLoop_physical_phase_threshold hfixed


-- created on 2026-10-23
