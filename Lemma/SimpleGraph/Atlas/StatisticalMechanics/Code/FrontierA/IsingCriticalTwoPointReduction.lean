import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointReduction
open Finset Set StatMech StatMech.FrontierA


/--
[boxBoundary_card_le_surfacePower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointReduction.lean)
-/
@[path]
private lemma boxBoundary_card_le_surfacePower_eq
  {d n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ((boxSV_vbF d n).card : ℝ) ≤ 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) := by
-- proof
  apply StatMech.FrontierA.boxBoundary_card_le_surfacePower d n hn

/--
[boxBoundaryEdges_card_le_surfacePower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointReduction.lean)
-/
@[path]
private lemma boxBoundaryEdges_card_le_surfacePower_eq
  {d n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ((boundaryEdges d (boxSV_boxF d n)).card : ℝ) ≤ 4 * d ^ 2 * (2 * (n : ℝ) + 1) ^ (d - 1) := by
-- proof
  apply StatMech.FrontierA.boxBoundaryEdges_card_le_surfacePower d n hn

/--
[boundaryMass_forces_pointwise_powerLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointReduction.lean)
-/
@[path]
private lemma boundaryMass_forces_pointwise_powerLower_eq
  {boundary : Finset X}
  {weight corr : X → ℝ}
  {targetValue : ℝ}
  {surfaceConstant edgeBound comparisonConstant radius : ℝ}
  {exponent : ℕ}
-- given
  (hsurface : (boundary.card : ℝ) ≤ surfaceConstant * radius ^ exponent)
  (hedge : 0 < edgeBound)
  (hcomparison : 0 < comparisonConstant)
  (hsurfaceConstant : 0 < surfaceConstant)
  (hradius : 0 < radius)
  (htarget : 0 ≤ targetValue)
  (hweightBound : ∀ x ∈ boundary, weight x ≤ edgeBound)
  (hcorrNonneg : ∀ x ∈ boundary, 0 ≤ corr x)
  (hcompare : ∀ x ∈ boundary, corr x ≤ comparisonConstant * targetValue)
  (hmass : 1 ≤ ∑ x ∈ boundary, weight x * corr x) :
-- imply
  1 / (surfaceConstant * edgeBound * comparisonConstant * radius ^ exponent) ≤ targetValue := by
-- proof
  apply StatMech.FrontierA.boundaryMass_forces_pointwise_powerLower boundary weight corr targetValue surfaceConstant edgeBound comparisonConstant radius exponent hsurface hedge hcomparison hsurfaceConstant hradius htarget hweightBound hcorrNonneg hcompare hmass

/--
[isingBoxSimonMass_forces_pointwise_powerLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointReduction.lean)
-/
@[path]
private lemma isingBoxSimonMass_forces_pointwise_powerLower_eq
  {d n : ℕ}
  {beta targetValue comparisonConstant : ℝ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hbeta : 0 < beta)
  (hcomparison : 0 < comparisonConstant)
  (htarget : 0 ≤ targetValue)
  (hphi : 1 ≤ phiIsing d beta (boxSV_boxF d n))
  (hshellCompare : ∀ e ∈ boundaryEdges d (boxSV_boxF d n), corrOriginInner d beta (boxSV_boxF d n) e.1 ≤ comparisonConstant * targetValue) :
-- imply
  1 / (4 * d ^ 2 * Real.tanh beta * comparisonConstant * (2 * (n : ℝ) + 1) ^ (d - 1)) ≤ targetValue := by
-- proof
  apply StatMech.FrontierA.isingBoxSimonMass_forces_pointwise_powerLower d n beta targetValue comparisonConstant hd hn hbeta hcomparison htarget hphi hshellCompare

/--
[greenComparison_gives_pointwise_powerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointReduction.lean)
-/
@[path]
private lemma greenComparison_gives_pointwise_powerUpper_eq
  {twoPoint greenValue infraredConstant greenConstant radius : ℝ}
  {exponent : ℕ}
-- given
  (hinfrared : 0 ≤ infraredConstant)
  (hcomparison : twoPoint ≤ infraredConstant * greenValue)
  (hgreen : greenValue ≤ greenConstant / radius ^ exponent) :
-- imply
  twoPoint ≤ infraredConstant * greenConstant / radius ^ exponent := by
-- proof
  apply StatMech.FrontierA.greenComparison_gives_pointwise_powerUpper twoPoint greenValue infraredConstant greenConstant radius exponent hinfrared hcomparison hgreen

/--
[criticalTwoPoint_powerBounds_of_reductions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointReduction.lean)
-/
@[path]
private lemma criticalTwoPoint_powerBounds_of_reductions_eq
  {d : ℕ}
  {boundary : Finset X}
  {weight corr : X → ℝ}
  {twoPoint greenValue : ℝ}
  {surfaceConstant edgeBound comparisonConstant radius : ℝ}
  {infraredConstant greenConstant : ℝ}
-- given
  (hsurface : (boundary.card : ℝ) ≤ surfaceConstant * radius ^ (d - 1))
  (hedge : 0 < edgeBound)
  (hcomparisonConstant : 0 < comparisonConstant)
  (hsurfaceConstant : 0 < surfaceConstant)
  (hradius : 0 < radius)
  (htwoPoint : 0 ≤ twoPoint)
  (hweightBound : ∀ x ∈ boundary, weight x ≤ edgeBound)
  (hcorrNonneg : ∀ x ∈ boundary, 0 ≤ corr x)
  (hshellCompare : ∀ x ∈ boundary, corr x ≤ comparisonConstant * twoPoint)
  (hmass : 1 ≤ ∑ x ∈ boundary, weight x * corr x)
  (hinfraredConstant : 0 ≤ infraredConstant)
  (hgreenComparison : twoPoint ≤ infraredConstant * greenValue)
  (hgreenDecay : greenValue ≤ greenConstant / radius ^ (d - 2)) :
-- imply
  1 / (surfaceConstant * edgeBound * comparisonConstant * radius ^ (d - 1)) ≤ twoPoint ∧ twoPoint ≤ infraredConstant * greenConstant / radius ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.criticalTwoPoint_powerBounds_of_reductions d boundary weight corr twoPoint greenValue surfaceConstant edgeBound comparisonConstant radius infraredConstant greenConstant hsurface hedge hcomparisonConstant hsurfaceConstant hradius htwoPoint hweightBound hcorrNonneg hshellCompare hmass hinfraredConstant hgreenComparison hgreenDecay


-- created on 2026-10-23
