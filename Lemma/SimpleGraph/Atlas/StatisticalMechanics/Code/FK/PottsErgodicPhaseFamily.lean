import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PottsErgodicPhaseFamily
open Filter MeasureTheory Set Topology StatMech StatMech.FK


/--
[pottsClusterSumJointMeasure_otherColor_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma pottsClusterSumJointMeasure_otherColor_real_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor a : Fin q}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure edgeMeasure]
  {x : Site d}
-- given
  (hba : boundaryColor ≠ a) :
-- imply
  (Measure.map Prod.fst (pottsClusterSumJointMeasure boundaryColor edgeMeasure)).real (pottsColorEvent d q x a) = (1 / (q : Real)) * edgeMeasure.real {omega | (cluster d omega x).Finite} := by
-- proof
  apply StatMech.FK.pottsClusterSumJointMeasure_otherColor_real boundaryColor a hba edgeMeasure x

/--
[freePottsClusterSumSpinProbabilityMeasure_isWeakLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma freePottsClusterSumSpinProbabilityMeasure_isWeakLimit_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {beta J : Real}
-- given
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hJ : 0 < J)
  (hfree : ((freeInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real {omega | (cluster d omega (origin d)).Infinite} = 0) :
-- imply
  let hp : 0 < 1 - Real.exp (-(beta * J)) := by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ) let hp1 : 1 - Real.exp (-(beta * J)) < 1 := by linarith [Real.exp_pos (-(beta * J))] exists phi : Nat -> Nat, StrictMono phi /\ Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J) atTop (nhds (freePottsClusterSumSpinProbabilityMeasure d q boundaryColor hp hp1)) := by
-- proof
  apply StatMech.FK.freePottsClusterSumSpinProbabilityMeasure_isWeakLimit d q hq boundaryColor beta J hbeta hJ hfree

/--
[freePottsClusterSumSpinProbabilityMeasure_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma freePottsClusterSumSpinProbabilityMeasure_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {p : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  IsErgodicFor (pottsSpinShift (d := d) (q := q)) (freePottsClusterSumSpinProbabilityMeasure d q boundaryColor hp hp1 : Measure _) := by
-- proof
  apply StatMech.FK.freePottsClusterSumSpinProbabilityMeasure_isErgodicFor hd boundaryColor hp hp1

/--
[wiredPottsClusterSumSpinProbabilityMeasure_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma wiredPottsClusterSumSpinProbabilityMeasure_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {p : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  IsErgodicFor (pottsSpinShift (d := d) (q := q)) (wiredPottsClusterSumSpinProbabilityMeasure d q boundaryColor hp hp1 : Measure _) := by
-- proof
  apply StatMech.FK.wiredPottsClusterSumSpinProbabilityMeasure_isErgodicFor hd boundaryColor hp hp1

/--
[freePottsClusterSumSpin_colorProbability_eq_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma freePottsClusterSumSpin_colorProbability_eq_inv_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor a : Fin q}
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfinite : ((freeInfiniteVolume d hp hp1 (by have hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) exact zero_lt_one.trans_le hqR) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real {omega | (cluster d omega (origin d)).Infinite} = 0) :
-- imply
  ((freePottsClusterSumSpinProbabilityMeasure d q boundaryColor hp hp1 : Measure _).real (pottsColorEvent d q (origin d) a)) = 1 / (q : Real) := by
-- proof
  apply StatMech.FK.freePottsClusterSumSpin_colorProbability_eq_inv boundaryColor a hp hp1 hfinite

/--
[wiredPottsClusterSumSpin_boundaryColorBias_eq_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma wiredPottsClusterSumSpin_boundaryColorBias_eq_fkTheta_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ((wiredPottsClusterSumSpinProbabilityMeasure d q boundaryColor hp hp1 : Measure _).real (pottsColorEvent d q (origin d) boundaryColor)) - 1 / (q : Real) = ((q : Real) - 1) / q * fkTheta d hp hp1 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (q := q) := by
-- proof
  apply StatMech.FK.wiredPottsClusterSumSpin_boundaryColorBias_eq_fkTheta boundaryColor hp hp1

/--
[wiredPottsClusterSumSpin_otherColorBias_eq_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma wiredPottsClusterSumSpin_otherColorBias_eq_fkTheta_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor a : Fin q}
  {p : Real}
-- given
  (hba : boundaryColor ≠ a)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ((wiredPottsClusterSumSpinProbabilityMeasure d q boundaryColor hp hp1 : Measure _).real (pottsColorEvent d q (origin d) a)) - 1 / (q : Real) = -(1 / (q : Real)) * fkTheta d hp hp1 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (q := q) := by
-- proof
  apply StatMech.FK.wiredPottsClusterSumSpin_otherColorBias_eq_fkTheta boundaryColor a hba hp hp1

/--
[exists_ergodic_potts_cluster_phase_candidate_family_with_exact_wired_bias](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma exists_ergodic_potts_cluster_phase_candidate_family_with_exact_wired_bias_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig d q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q)), IsErgodicFor (pottsSpinShift (d := d) (q := q)) (muFree : Measure _) ∧ (∀ b, IsErgodicFor (pottsSpinShift (d := d) (q := q)) (muWired b : Measure _)) ∧ (∀ b, ((muWired b : ProbabilityMeasure (PottsConfig d q)) : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) b) - 1 / (q : Real) = ((q : Real) - 1) / q * fkTheta d hp hp1 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (q := q)) ∧ ∀ b a, b ≠ a -> ((muWired b : ProbabilityMeasure (PottsConfig d q)) : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) a) - 1 / (q : Real) = -(1 / (q : Real)) * fkTheta d hp hp1 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (q := q) := by
-- proof
  apply StatMech.FK.exists_ergodic_potts_cluster_phase_candidate_family_with_exact_wired_bias d q hd hp hp1

/--
[exists_ergodic_critical_potts_cluster_phase_candidate_family_with_exact_wired_bias](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma exists_ergodic_critical_potts_cluster_phase_candidate_family_with_exact_wired_bias_eq
  {q : Nat}
  [NeZero q]
-- given
  (hq : 4 < q) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)), IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muFree : Measure _) ∧ (∀ b, IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muWired b : Measure _)) ∧ (∀ b, ((muWired b : ProbabilityMeasure (PottsConfig 2 q)) : Measure (PottsConfig 2 q)).real (pottsColorEvent 2 q (origin 2) b) - 1 / (q : Real) = ((q : Real) - 1) / q * fkTheta 2 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2 (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q)) ∧ ∀ b a, b ≠ a -> ((muWired b : ProbabilityMeasure (PottsConfig 2 q)) : Measure (PottsConfig 2 q)).real (pottsColorEvent 2 q (origin 2) a) - 1 / (q : Real) = -(1 / (q : Real)) * fkTheta 2 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2 (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q) := by
-- proof
  apply StatMech.FK.exists_ergodic_critical_potts_cluster_phase_candidate_family_with_exact_wired_bias q hq

/--
[exists_pairwise_distinct_ergodic_potts_cluster_phase_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma exists_pairwise_distinct_ergodic_potts_cluster_phase_family_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfree : ((freeInfiniteVolume d hp hp1 (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real {omega | (cluster d omega (origin d)).Infinite} = 0)
  (hwired : 0 < fkTheta d hp hp1 (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig d q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q)), IsErgodicFor (pottsSpinShift (d := d) (q := q)) (muFree : Measure _) ∧ (forall b, IsErgodicFor (pottsSpinShift (d := d) (q := q)) (muWired b : Measure _)) ∧ (forall b, muFree ≠ muWired b) ∧ forall b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FK.exists_pairwise_distinct_ergodic_potts_cluster_phase_family d q hd hq hp hp1 hfree hwired

/--
[exists_pairwise_distinct_ergodic_potts_cluster_phase_family_of_firstOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma exists_pairwise_distinct_ergodic_potts_cluster_phase_family_of_firstOrder_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfirst : IsFirstOrderTransition d hp hp1 (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig d q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig d q)), IsErgodicFor (pottsSpinShift (d := d) (q := q)) (muFree : Measure _) ∧ (forall b, IsErgodicFor (pottsSpinShift (d := d) (q := q)) (muWired b : Measure _)) ∧ (forall b, muFree ≠ muWired b) ∧ forall b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FK.exists_pairwise_distinct_ergodic_potts_cluster_phase_family_of_firstOrder d q hd hq hp hp1 hfirst

/--
[exists_pairwise_distinct_ergodic_critical_potts_cluster_phase_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsErgodicPhaseFamily.lean)
-/
@[path]
private lemma exists_pairwise_distinct_ergodic_critical_potts_cluster_phase_family_eq
  {q : Nat}
  [NeZero q]
-- given
  (hq : 4 < q)
  (hfirst : IsFirstOrderTransition 2 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)).2 (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)), IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muFree : Measure _) ∧ (forall b, IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muWired b : Measure _)) ∧ (forall b, muFree ≠ muWired b) ∧ forall b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FK.exists_pairwise_distinct_ergodic_critical_potts_cluster_phase_family q hq hfirst


-- created on 2026-10-23
