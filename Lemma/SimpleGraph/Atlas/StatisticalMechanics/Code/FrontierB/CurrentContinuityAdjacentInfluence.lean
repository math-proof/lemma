import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentContinuityAdjacentInfluence
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[beta_mul_adjacent_gap_le_fixed_boundary_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAdjacentInfluence.lean)
-/
@[path]
private lemma beta_mul_adjacent_gap_le_fixed_boundary_union_eq
  {d m : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hxy : (hypercubicLattice d).Adj x y)
  (hm : 1 ≤ m)
  (hx : x ∈ box d (m - 1))
  (hy : y ∈ box d (m - 1)) :
-- imply
  beta * (currentContinuityPlusTwoPoint d beta x y - currentContinuityFreeTwoPoint d beta x y) ≤ (((infinitePlusCurrentMeasure d beta hbeta.le).prod (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real (superposedCurrentTrace ⁻¹' (traceBoundaryConnectionEvent m x ∪ traceBoundaryConnectionEvent m y))) := by
-- proof
  apply StatMech.FrontierB.beta_mul_adjacent_gap_le_fixed_boundary_union d m beta hbeta x y hxy hm hx hy

/--
[currentContinuityMixedTraceLaw_clusterInfinite_real_eq_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAdjacentInfluence.lean)
-/
@[path]
private lemma currentContinuityMixedTraceLaw_clusterInfinite_real_eq_percolation_eq
  {d : ℕ}
  {beta : ℝ}
  {x : Site d}
-- given
  (hbeta : 0 < beta) :
-- imply
  (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (StatMech.FK.clusterInfiniteEvent d x) = (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (percolationEvent d) := by
-- proof
  apply StatMech.FrontierB.currentContinuityMixedTraceLaw_clusterInfinite_real_eq_percolation d beta hbeta x

/--
[beta_mul_currentContinuity_adjacent_gap_le_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAdjacentInfluence.lean)
-/
@[path]
private lemma beta_mul_currentContinuity_adjacent_gap_le_percolation_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hxy : (hypercubicLattice d).Adj x y) :
-- imply
  beta * (currentContinuityPlusTwoPoint d beta x y - currentContinuityFreeTwoPoint d beta x y) ≤ 2 * (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (percolationEvent d) := by
-- proof
  apply StatMech.FrontierB.beta_mul_currentContinuity_adjacent_gap_le_percolation d beta hbeta x y hxy

/--
[currentContinuity_adjacent_gap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAdjacentInfluence.lean)
-/
@[path]
private lemma currentContinuity_adjacent_gap_nonneg_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hxy : (hypercubicLattice d).Adj x y) :
-- imply
  0 ≤ currentContinuityPlusTwoPoint d beta x y - currentContinuityFreeTwoPoint d beta x y := by
-- proof
  apply StatMech.FrontierB.currentContinuity_adjacent_gap_nonneg d beta hbeta x y hxy

/--
[currentContinuity_adjacent_eq_of_no_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityAdjacentInfluence.lean)
-/
@[path]
private lemma currentContinuity_adjacent_eq_of_no_percolation_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hnoperco : (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (percolationEvent d) = 0)
  (hxy : (hypercubicLattice d).Adj x y) :
-- imply
  currentContinuityPlusTwoPoint d beta x y = currentContinuityFreeTwoPoint d beta x y := by
-- proof
  apply StatMech.FrontierB.currentContinuity_adjacent_eq_of_no_percolation d beta hbeta hnoperco x y hxy


-- created on 2026-10-23
