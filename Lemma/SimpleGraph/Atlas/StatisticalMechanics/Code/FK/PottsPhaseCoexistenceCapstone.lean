import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsPhaseCoexistenceCapstone
open Filter MeasureTheory Topology StatMech StatMech.FK


/--
[pottsSelfDualInverseTemperature_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsPhaseCoexistenceCapstone.lean)
-/
@[path]
private lemma pottsSelfDualInverseTemperature_pos_eq
  {q : Nat}
  {J : Real}
-- given
  (hq : 0 < q)
  (hJ : 0 < J) :
-- imply
  0 < pottsSelfDualInverseTemperature q J := by
-- proof
  apply StatMech.FK.pottsSelfDualInverseTemperature_pos hq hJ

/--
[one_sub_exp_neg_pottsSelfDualInverseTemperature_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsPhaseCoexistenceCapstone.lean)
-/
@[path]
private lemma one_sub_exp_neg_pottsSelfDualInverseTemperature_mul_eq
  {q : Nat}
  {J : Real}
-- given
  (hq : 0 < q)
  (hJ : 0 < J) :
-- imply
  1 - Real.exp (-(pottsSelfDualInverseTemperature q J * J)) = BeffaraDC.selfDualPoint q := by
-- proof
  apply StatMech.FK.one_sub_exp_neg_pottsSelfDualInverseTemperature_mul hq hJ

/--
[exists_potts_phase_candidate_family_with_exact_oneSite_bias](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsPhaseCoexistenceCapstone.lean)
-/
@[path]
private lemma exists_potts_phase_candidate_family_with_exact_oneSite_bias_eq
  {d q : Nat}
  [NeZero q]
  {beta J : Real}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hJ : 0 < J) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig d q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q)) (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat), StrictMono phiFree ∧ Tendsto (fun n => freePottsFiniteMeasure d (phiFree n) q beta J) atTop (nhds muFree) ∧ (∀ b, StrictMono (phiWired b) ∧ Tendsto (fun n => wiredPottsFiniteMeasure d (phiWired b n) q b beta J) atTop (nhds (muWired b))) ∧ (∀ b, (muFree : Measure (PottsConfig d q)).real (pottsColorEvent d q (StatMech.Percolation.origin d) b) = 1 / (q : Real)) ∧ (∀ b, ((muWired b : ProbabilityMeasure (PottsConfig d q)) : Measure (PottsConfig d q)).real (pottsColorEvent d q (StatMech.Percolation.origin d) b) - 1 / (q : Real) = ((q : Real) - 1) / q * fkTheta d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q)) ∧ ∀ b a, a ≠ b -> ((muWired b : ProbabilityMeasure (PottsConfig d q)) : Measure (PottsConfig d q)).real (pottsColorEvent d q (StatMech.Percolation.origin d) a) - 1 / (q : Real) = -(1 / (q : Real)) * fkTheta d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q) := by
-- proof
  apply StatMech.FK.exists_potts_phase_candidate_family_with_exact_oneSite_bias d q hd hq beta J hbeta hJ

/--
[exists_critical_potts_phase_candidate_family_with_exact_oneSite_bias](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsPhaseCoexistenceCapstone.lean)
-/
@[path]
private lemma exists_critical_potts_phase_candidate_family_with_exact_oneSite_bias_eq
  {q : Nat}
  [NeZero q]
  {J : Real}
-- given
  (hq : 4 < q)
  (hJ : 0 < J) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)) (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat), StrictMono phiFree ∧ Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧ (∀ b, StrictMono (phiWired b) ∧ Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b (pottsSelfDualInverseTemperature q J) J) atTop (nhds (muWired b))) ∧ (∀ b, (muFree : Measure (PottsConfig 2 q)).real (pottsColorEvent 2 q (StatMech.Percolation.origin 2) b) = 1 / (q : Real)) ∧ (∀ b, ((muWired b : ProbabilityMeasure (PottsConfig 2 q)) : Measure (PottsConfig 2 q)).real (pottsColorEvent 2 q (StatMech.Percolation.origin 2) b) - 1 / (q : Real) = ((q : Real) - 1) / q * fkTheta 2 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2 (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q)) ∧ ∀ b a, a ≠ b -> ((muWired b : ProbabilityMeasure (PottsConfig 2 q)) : Measure (PottsConfig 2 q)).real (pottsColorEvent 2 q (StatMech.Percolation.origin 2) a) - 1 / (q : Real) = -(1 / (q : Real)) * fkTheta 2 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2 (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q) := by
-- proof
  apply StatMech.FK.exists_critical_potts_phase_candidate_family_with_exact_oneSite_bias q hq J hJ

/--
[exists_pairwise_distinct_potts_phase_family_of_fkTheta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsPhaseCoexistenceCapstone.lean)
-/
@[path]
private lemma exists_pairwise_distinct_potts_phase_family_of_fkTheta_pos_eq
  {d q : Nat}
  [NeZero q]
  {beta J : Real}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hJ : 0 < J)
  (htheta : 0 < fkTheta d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig d q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q)) (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat), Tendsto (fun n => freePottsFiniteMeasure d (phiFree n) q beta J) atTop (nhds muFree) ∧ (∀ b, StrictMono (phiWired b) ∧ Tendsto (fun n => wiredPottsFiniteMeasure d (phiWired b n) q b beta J) atTop (nhds (muWired b))) ∧ (∀ b, muFree ≠ muWired b) ∧ ∀ b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FK.exists_pairwise_distinct_potts_phase_family_of_fkTheta_pos d q hd hq beta J hbeta hJ htheta

/--
[exists_pairwise_distinct_critical_potts_phase_family_of_selfDualTheta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsPhaseCoexistenceCapstone.lean)
-/
@[path]
private lemma exists_pairwise_distinct_critical_potts_phase_family_of_selfDualTheta_pos_eq
  {q : Nat}
  [NeZero q]
  {J : Real}
-- given
  (hq : 4 < q)
  (hJ : 0 < J)
  (htheta : 0 < fkTheta 2 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2 (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)) (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat), Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧ (∀ b, StrictMono (phiWired b) ∧ Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b (pottsSelfDualInverseTemperature q J) J) atTop (nhds (muWired b))) ∧ (∀ b, muFree ≠ muWired b) ∧ ∀ b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FK.exists_pairwise_distinct_critical_potts_phase_family_of_selfDualTheta_pos q hq J hJ htheta


-- created on 2026-10-23
