import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentContinuityMagnetizationFK
open Filter MeasureTheory Set Topology BoundedContinuousFunction StatMech StatMech.FrontierB


/--
[allClustersEven_pair_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityMagnetizationFK.lean)
-/
@[path]
private lemma allClustersEven_pair_iff_reachable_eq
  {d : Nat}
  [DecidableEq V]
  {G : SimpleGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  AllClustersEven G omega ({x, y} : Finset V) ↔ (openSub G omega).Reachable x y := by
-- proof
  apply StatMech.FrontierB.allClustersEven_pair_iff_reachable G omega x y hxy

/--
[currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityMagnetizationFK.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint_eq
  {d : Nat}
  {beta : Real}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hxy : x ≠ y) :
-- imply
  currentContinuityFreeTwoPoint d beta x y = infiniteTwoPointReal (freeInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure _) x y := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint beta hbeta hd x y hxy

/--
[freeInfiniteVolume_noPercolation_of_currentContinuityFreeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityMagnetizationFK.lean)
-/
@[path]
private lemma freeInfiniteVolume_noPercolation_of_currentContinuityFreeLROZero_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta) :
-- imply
  (freeInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure _).real (percolationEvent d) = 0 := by
-- proof
  apply StatMech.FrontierB.freeInfiniteVolume_noPercolation_of_currentContinuityFreeLROZero beta hbeta hd hLRO

/--
[currentContinuity_magnetization_and_phase_eq_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityMagnetizationFK.lean)
-/
@[path]
private lemma currentContinuity_magnetization_and_phase_eq_of_freeLROZero_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta) :
-- imply
  magnetization d beta = 0 ∧ (plusState d beta 0 : Measure (ConfigSpace (Site d))) = (minusState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_magnetization_and_phase_eq_of_freeLROZero beta hbeta hd hLRO

/--
[currentContinuity_gibbs_unique_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityMagnetizationFK.lean)
-/
@[path]
private lemma currentContinuity_gibbs_unique_of_freeLROZero_eq
  {d : Nat}
  {beta : Real}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta)
  (hmu : IsDLRState d beta 0 mu) :
-- imply
  mu = (minusState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_gibbs_unique_of_freeLROZero beta hbeta hd hLRO mu hmu

/--
[currentContinuity_localExpectation_tendsto_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityMagnetizationFK.lean)
-/
@[path]
private lemma currentContinuity_localExpectation_tendsto_of_freeLROZero_eq
  {d : Nat}
  {beta : Real}
  {mu : Nat → ProbabilityMeasure (ConfigSpace (Site d))}
  {muLim : ProbabilityMeasure (ConfigSpace (Site d))}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta)
  (hconv : WeakConvergesTo mu muLim)
  (hDLR : IsDLRState d beta 0 (muLim : Measure _)) :
-- imply
  Tendsto (fun n => ∫ omega, f omega ∂(mu n : Measure _)) atTop (nhds (∫ omega, f omega ∂(minusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_localExpectation_tendsto_of_freeLROZero beta hbeta hd hLRO mu muLim hconv hDLR f


-- created on 2026-10-23
