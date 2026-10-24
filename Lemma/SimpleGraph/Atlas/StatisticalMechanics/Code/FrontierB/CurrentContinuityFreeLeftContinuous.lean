import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[continuous_currentContinuityFreeBoxTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFreeLeftContinuous.lean)
-/
@[path]
private lemma continuous_currentContinuityFreeBoxTwoPoint_eq
  {d : Nat}
  {n : Nat}
  {x y : Site d}
-- given
  (hxy : ({x, y} : Finset (Site d)) ⊆ Ising.boxFinset d n) :
-- imply
  Continuous (fun beta => currentContinuityFreeBoxTwoPoint d n beta x y) := by
-- proof
  apply StatMech.FrontierB.continuous_currentContinuityFreeBoxTwoPoint n x y hxy

/--
[currentContinuityFreeBoxTwoPoint_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFreeLeftContinuous.lean)
-/
@[path]
private lemma currentContinuityFreeBoxTwoPoint_mono_beta_eq
  {d : Nat}
  {beta gamma : Real}
  {n : Nat}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hbg : beta ≤ gamma)
  (hxy : ({x, y} : Finset (Site d)) ⊆ Ising.boxFinset d n) :
-- imply
  currentContinuityFreeBoxTwoPoint d n beta x y ≤ currentContinuityFreeBoxTwoPoint d n gamma x y := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeBoxTwoPoint_mono_beta hbeta hbg n x y hxy

/--
[currentContinuityFreeBoxTwoPoint_le_freeTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFreeLeftContinuous.lean)
-/
@[path]
private lemma currentContinuityFreeBoxTwoPoint_le_freeTwoPoint_eq
  {d : Nat}
  {beta : Real}
  {n : Nat}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hxy : ({x, y} : Finset (Site d)) ⊆ Ising.boxFinset d n) :
-- imply
  currentContinuityFreeBoxTwoPoint d n beta x y ≤ currentContinuityFreeTwoPoint d beta x y := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeBoxTwoPoint_le_freeTwoPoint beta hbeta n x y hxy

/--
[currentContinuityFreeTwoPoint_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFreeLeftContinuous.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_mono_beta_eq
  {d : Nat}
  {beta gamma : Real}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hbg : beta ≤ gamma) :
-- imply
  currentContinuityFreeTwoPoint d beta x y ≤ currentContinuityFreeTwoPoint d gamma x y := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeTwoPoint_mono_beta hbeta hbg x y

/--
[currentContinuityFreeTwoPoint_tendsto_fromBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFreeLeftContinuous.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_tendsto_fromBelow_eq
  {d : Nat}
  {beta0 : Real}
  {x y : Site d}
-- given
  (hbeta0 : 0 < beta0) :
-- imply
  Tendsto (fun n : Nat => currentContinuityFreeTwoPoint d (beta0 - 1 / (n + 1 : Real)) x y) atTop (nhds (currentContinuityFreeTwoPoint d beta0 x y)) := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeTwoPoint_tendsto_fromBelow beta0 hbeta0 x y

/--
[currentContinuityFreeLROZero_of_subcritical_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFreeLeftContinuous.lean)
-/
@[path]
private lemma currentContinuityFreeLROZero_of_subcritical_bound_eq
  {d : Nat}
  {beta0 : Real}
  {majorant : Site d → Real}
-- given
  (hbeta0 : 0 < beta0)
  (hbound : ∀ beta, 0 < beta → beta < beta0 → ∀ x, |currentContinuityFreeTwoPoint d beta (Percolation.origin d) x| ≤ majorant x)
  (hdecay : ∀ epsilon : Real, 0 < epsilon → ∃ R : Nat, ∀ x : Site d, x ∉ box d R → majorant x < epsilon) :
-- imply
  CurrentContinuityFreeLROZero d beta0 := by
-- proof
  apply StatMech.FrontierB.currentContinuityFreeLROZero_of_subcritical_bound beta0 hbeta0 majorant hbound hdecay


-- created on 2026-10-23
