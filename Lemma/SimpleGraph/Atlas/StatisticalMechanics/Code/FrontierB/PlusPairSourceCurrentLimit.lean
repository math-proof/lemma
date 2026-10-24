import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.PlusPairSourceCurrentLimit
open Filter MeasureTheory StatMech StatMech.FrontierB


/--
[growingPlusPairSourceCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceCurrentLimit.lean)
-/
@[path]
private lemma growingPlusPairSourceCurrentMeasure_edge_inverse_tail_le_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
  {k : ℕ}
  {e : Sym2 (Site d)}
  {K : ℕ}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y)
  (hK : 0 < K) :
-- imply
  (growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy k : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m e} ≤ ENNReal.ofReal (2 * Real.exp beta) / K := by
-- proof
  apply StatMech.FrontierB.growingPlusPairSourceCurrentMeasure_edge_inverse_tail_le d N beta hbeta x y hx hy hxy k e K hK

/--
[growingPlusPairSourceCurrentMeasure_tight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceCurrentLimit.lean)
-/
@[path]
private lemma growingPlusPairSourceCurrentMeasure_tight_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  IsTightMeasureSet (Set.range fun k => (growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy k : Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FrontierB.growingPlusPairSourceCurrentMeasure_tight d N beta hbeta x y hx hy hxy

/--
[growingPlusPairSourceCurrentMeasure_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceCurrentLimit.lean)
-/
@[path]
private lemma growingPlusPairSourceCurrentMeasure_subsequence_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges ((growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nu := by
-- proof
  apply StatMech.FrontierB.growingPlusPairSourceCurrentMeasure_subsequence d N beta hbeta x y hx hy hxy

/--
[growingPlusPairSourceCurrentMeasure_subsequence_with_cylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceCurrentLimit.lean)
-/
@[path]
private lemma growingPlusPairSourceCurrentMeasure_subsequence_with_cylinders_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges ((growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nu ∧ ∀ (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)), Tendsto (fun k => growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy (phi k) (currentCylinder S A)) atTop (nhds (nu (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.growingPlusPairSourceCurrentMeasure_subsequence_with_cylinders d N beta hbeta x y hx hy hxy


-- created on 2026-10-23
