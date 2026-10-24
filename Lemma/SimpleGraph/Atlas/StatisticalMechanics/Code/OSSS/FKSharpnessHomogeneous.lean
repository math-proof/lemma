import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.FKSharpnessHomogeneous
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessHomogeneous


/--
[wiredBoxBoundaryMass_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessHomogeneous.lean)
-/
@[path]
private lemma wiredBoxBoundaryMass_lt_one_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  (wiredFiniteMeasure d n (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) < 1 := by
-- proof
  apply StatMech.OSSS.FKSharpnessHomogeneous.wiredBoxBoundaryMass_lt_one d n q beta hq hbeta

/--
[wiredBoxBoundary_exponential_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessHomogeneous.lean)
-/
@[path]
private lemma wiredBoxBoundary_exponential_decay_eq
  {d : Nat}
  {q beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hsub : beta < fkCriticalBetaQ d q) :
-- imply
  exists Q : Real, 0 < Q ∧ forall n : Nat, 1 <= n -> (wiredFiniteMeasure d n (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) <= Real.exp (-((n : Real) / Q)) := by
-- proof
  apply StatMech.OSSS.FKSharpnessHomogeneous.wiredBoxBoundary_exponential_decay d q beta hd hq hbeta hsub

/--
[betaFKThetaQ_meanField_near_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessHomogeneous.lean)
-/
@[path]
private lemma betaFKThetaQ_meanField_near_critical_eq
  {d : Nat}
  {q : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q) :
-- imply
  exists c : Real, 0 < c ∧ forall beta, fkCriticalBetaQ d q <= beta -> beta <= fkCriticalBetaQ d q + 1 -> c * (beta - fkCriticalBetaQ d q) <= betaFKThetaQ d q hq beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessHomogeneous.betaFKThetaQ_meanField_near_critical d q hd hq

/--
[fkSharpness_homogeneous_physical_boxes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessHomogeneous.lean)
-/
@[path]
private lemma fkSharpness_homogeneous_physical_boxes_eq
  {d : Nat}
  {q : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q) :
-- imply
  (exists c : Real, 0 < c ∧ forall beta, fkCriticalBetaQ d q <= beta -> beta <= fkCriticalBetaQ d q + 1 -> c * (beta - fkCriticalBetaQ d q) <= betaFKThetaQ d q hq beta) ∧ (forall beta (hbeta : 0 < beta), beta < fkCriticalBetaQ d q -> exists Q : Real, 0 < Q ∧ forall n : Nat, 1 <= n -> (wiredFiniteMeasure d n (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) <= Real.exp (-((n : Real) / Q))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessHomogeneous.fkSharpness_homogeneous_physical_boxes d q hd hq


-- created on 2026-10-23
