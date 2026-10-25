import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityLimits
open MeasureTheory Filter Topology StatMech StatMech.FrontierB


/--
[finiteLatticeEdges_subset_bondFinsetTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityLimits.lean)
-/
@[path]
private lemma finiteLatticeEdges_subset_bondFinsetTouch_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  ∃ N, F ⊆ bondFinsetTouch d N := by
-- proof
  apply StatMech.FrontierB.finiteLatticeEdges_subset_bondFinsetTouch d F hF

/--
[plusBoxCurrentMeasure_parityAvoid_full_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityLimits.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_parityAvoid_full_tendsto_eq
  {d : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 ≤ beta)
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  Tendsto (fun n => (plusBoxCurrentMeasure d n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder F)) atTop (nhds (ENNReal.ofReal ((∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) * Real.cosh beta ^ F.card))) := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_parityAvoid_full_tendsto d beta hbeta F hF

/--
[freeBoxCurrentMeasure_parityAvoid_full_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityLimits.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_parityAvoid_full_tendsto_eq
  {d : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 ≤ beta)
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet) :
-- imply
  Tendsto (fun n => (freeBoxCurrentMeasure d n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder F)) atTop (nhds (ENNReal.ofReal ((∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) * Real.cosh beta ^ F.card))) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_parityAvoid_full_tendsto d beta hbeta F hF


-- created on 2026-10-23
