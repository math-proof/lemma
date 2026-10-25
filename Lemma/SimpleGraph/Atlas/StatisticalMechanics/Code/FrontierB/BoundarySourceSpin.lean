import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.BoundarySourceSpin
open StatMech StatMech.FrontierB


/--
[interiorSpinSum_monomial_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceSpin.lean)
-/
@[path]
private lemma interiorSpinSum_monomial_insert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {interior A : Finset V}
  {n : Sharpness.Current V}
-- given
  (hA : A ⊆ interior) :
-- imply
  (∑ s : ConfigSpace ↑interior, spinProd A (extendInteriorPlus interior s) * ∏ e ∈ G.edgeFinset, bond (extendInteriorPlus interior s) e ^ n e) = if (sources G n) ∩ interior = A then (2 : ℝ) ^ interior.card else 0 := by
-- proof
  apply StatMech.FrontierB.interiorSpinSum_monomial_insert G interior A hA n

/--
[boundarySpinNumerator_eq_boundarySourceCurrentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceSpin.lean)
-/
@[path]
private lemma boundarySpinNumerator_eq_boundarySourceCurrentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior A : Finset V}
-- given
  (hA : A ⊆ interior) :
-- imply
  (∑ s : ConfigSpace ↑interior, spinProd A (extendInteriorPlus interior s) * boltzmannJ G beta J (extendInteriorPlus interior s)) = (2 : ℝ) ^ interior.card * boundarySourceCurrentSum G beta J interior A := by
-- proof
  apply StatMech.FrontierB.boundarySpinNumerator_eq_boundarySourceCurrentSum G beta J interior A hA

/--
[boundarySourceCurrentSum_div_boundaryCurrentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceSpin.lean)
-/
@[path]
private lemma boundarySourceCurrentSum_div_boundaryCurrentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior A : Finset V}
-- given
  (hA : A ⊆ interior) :
-- imply
  boundarySourceCurrentSum G beta J interior A / boundaryCurrentSum G beta J interior = (∑ s : ConfigSpace ↑interior, spinProd A (extendInteriorPlus interior s) * boltzmannJ G beta J (extendInteriorPlus interior s)) / boundaryPartitionJ G beta J interior := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentSum_div_boundaryCurrentSum G beta J interior A hA


-- created on 2026-10-23
