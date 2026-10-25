import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityReduction.Part2
open Filter MeasureTheory Set Topology BoundedContinuousFunction StatMech StatMech.FrontierB


/--
[independentSuperposedTraceLaw_real_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma independentSuperposedTraceLaw_real_apply_eq
  {d : ℕ}
  [Countable E]
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {A : Set (ConfigSpace E)}
-- given
  (hA : MeasurableSet A) :
-- imply
  (independentSuperposedTraceLaw mu nu : Measure _).real A = (mu.prod nu : Measure _).real (superposedCurrentTrace ⁻¹' A) := by
-- proof
  apply StatMech.FrontierB.independentSuperposedTraceLaw_real_apply mu nu hA

/--
[currentContinuity_mixed_twoPoint_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma currentContinuity_mixed_twoPoint_identity_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hunique : (currentContinuityMixedTraceLaw d beta hbeta : Measure _) (atLeastTwoInfinite d) = 0)
  (hxy : x ≠ y) :
-- imply
  currentContinuityPlusTwoPoint d beta x y * currentContinuityFreeTwoPoint d beta x y = StatMech.FK.infiniteTwoPointReal (currentContinuityMixedTraceLaw d beta hbeta : Measure _) x y := by
-- proof
  apply StatMech.FrontierB.currentContinuity_mixed_twoPoint_identity beta hbeta hunique x y hxy

/--
[currentContinuityPlusTwoPoint_eq_plusCorr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma currentContinuityPlusTwoPoint_eq_plusCorr_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hxy : x ≠ y) :
-- imply
  currentContinuityPlusTwoPoint d beta x y = plusCorr d beta x y := by
-- proof
  apply StatMech.FrontierB.currentContinuityPlusTwoPoint_eq_plusCorr beta x y hxy

/--
[currentContinuity_no_persistent_connectivity_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma currentContinuity_no_persistent_connectivity_of_freeLROZero_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hunique : (currentContinuityMixedTraceLaw d beta hbeta : Measure _) (atLeastTwoInfinite d) = 0)
  (hLRO : CurrentContinuityFreeLROZero d beta) :
-- imply
  ¬ CurrentContinuityConnectivityPersists d (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_no_persistent_connectivity_of_freeLROZero beta hbeta hunique hLRO

/--
[currentContinuity_no_percolation_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma currentContinuity_no_percolation_of_freeLROZero_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hunique : (currentContinuityMixedTraceLaw d beta hbeta : Measure _) (atLeastTwoInfinite d) = 0)
  (hprinciple : CurrentContinuityPercolationPrinciple d (currentContinuityMixedTraceLaw d beta hbeta : Measure _))
  (hLRO : CurrentContinuityFreeLROZero d beta) :
-- imply
  (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (percolationEvent d) = 0 := by
-- proof
  apply StatMech.FrontierB.currentContinuity_no_percolation_of_freeLROZero beta hbeta hunique hprinciple hLRO

/--
[currentContinuity_freePlus_no_percolation_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma currentContinuity_freePlus_no_percolation_zero_beta_eq
  {d : ℕ} :
-- imply
  (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d 0 le_rfl) (infiniteFreeCurrentMeasure d 0 le_rfl) : Measure _).real (percolationEvent d) = 0 := by
-- proof
  apply StatMech.FrontierB.currentContinuity_freePlus_no_percolation_zero_beta

/--
[currentContinuity_twoPoint_eq_of_no_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma currentContinuity_twoPoint_eq_of_no_percolation_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hinfluence : CurrentContinuityTwoPointInfluenceBound d beta hbeta)
  (hnoperco : (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (percolationEvent d) = 0) :
-- imply
  currentContinuityPlusTwoPoint d beta x y = currentContinuityFreeTwoPoint d beta x y := by
-- proof
  apply StatMech.FrontierB.currentContinuity_twoPoint_eq_of_no_percolation beta hbeta hinfluence hnoperco x y

/--
[currentContinuity_magnetization_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma currentContinuity_magnetization_eq_zero_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hLRO : CurrentContinuityFreeLROZero d beta)
  (htwo : ∀ x : Site d, currentContinuityPlusTwoPoint d beta (Percolation.origin d) x = currentContinuityFreeTwoPoint d beta (Percolation.origin d) x)
  (hd : 1 ≤ d) :
-- imply
  magnetization d beta = 0 := by
-- proof
  apply StatMech.FrontierB.currentContinuity_magnetization_eq_zero beta hbeta hLRO htwo hd

/--
[currentContinuity_core_of_probabilistic_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma currentContinuity_core_of_probabilistic_inputs_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hunique : (currentContinuityMixedTraceLaw d beta hbeta : Measure _) (atLeastTwoInfinite d) = 0)
  (hprinciple : CurrentContinuityPercolationPrinciple d (currentContinuityMixedTraceLaw d beta hbeta : Measure _))
  (hinfluence : CurrentContinuityTwoPointInfluenceBound d beta hbeta)
  (hLRO : CurrentContinuityFreeLROZero d beta) :
-- imply
  (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (percolationEvent d) = 0 ∧ (∀ x y : Site d, currentContinuityPlusTwoPoint d beta x y = currentContinuityFreeTwoPoint d beta x y) ∧ magnetization d beta = 0 := by
-- proof
  apply StatMech.FrontierB.currentContinuity_core_of_probabilistic_inputs beta hbeta hd hunique hprinciple hinfluence hLRO

/--
[currentContinuity_localExpectation_tendsto_of_unique_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean)
-/
@[path]
private lemma currentContinuity_localExpectation_tendsto_of_unique_limit_eq
  {d : ℕ}
  {beta : ℝ}
  {mu : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {muLim : ProbabilityMeasure (ConfigSpace (Site d))}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hconv : WeakConvergesTo mu muLim)
  (hDLR : IsDLRState d beta 0 (muLim : Measure _))
  (hphase : (plusState d beta 0 : Measure (ConfigSpace (Site d))) = (minusState d beta 0 : Measure (ConfigSpace (Site d)))) :
-- imply
  Tendsto (fun n => ∫ omega, f omega ∂(mu n : Measure _)) atTop (nhds (∫ omega, f omega ∂(minusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_localExpectation_tendsto_of_unique_limit beta hbeta mu muLim hconv hDLR hphase f


-- created on 2026-10-23
