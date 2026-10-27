import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxCurrentParity
open MeasureTheory Filter Topology StatMech StatMech.FrontierB


/--
[boxGraph_eq_sctBoxGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxCurrentParity.lean)
-/
@[path]
private lemma boxGraph_eq_sctBoxGraph_eq
  {d n : ℕ} :
-- imply
  StatMech.FK.boxGraph d n = sctBoxGraph d n := by
-- proof
  apply StatMech.FrontierB.boxGraph_eq_sctBoxGraph d n

/--
[bond_boxConfig_eq_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxCurrentParity.lean)
-/
@[path]
private lemma bond_boxConfig_eq_glue_eq
  {d n : ℕ}
  {tau : ConfigSpace (StatMech.FK.boxVerts d n)}
  {e : Sym2 (StatMech.FK.boxVerts d n)} :
-- imply
  bond tau e = bond (glue (minusField d) tau) (StatMech.FK.edgeIncl d n e) := by
-- proof
  apply StatMech.FrontierB.bond_boxConfig_eq_glue d n tau e

/--
[edgeSpinSum_boxPullbackEdges_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxCurrentParity.lean)
-/
@[path]
private lemma edgeSpinSum_boxPullbackEdges_free_eq
  {d n : ℕ}
  {F : Finset (Sym2 (Site d))}
  {tau : ConfigSpace (StatMech.FK.boxVerts d (n + 1))}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  edgeSpinSum (boxPullbackEdges d n F) tau = edgeSpinSum F (glue (minusField d) tau) := by
-- proof
  apply StatMech.FrontierB.edgeSpinSum_boxPullbackEdges_free d n F hF tau

/--
[freeSpinExpectation_box_eq_freeIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxCurrentParity.lean)
-/
@[path]
private lemma freeSpinExpectation_box_eq_freeIntegral_eq
  {d n : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  ((∑ s : ConfigSpace (StatMech.FK.boxVerts d (n + 1)), boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) s * Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F) s)) / partitionJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)) = ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(freeMeasure d (n + 1) beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.freeSpinExpectation_box_eq_freeIntegral d n beta F hF

/--
[freeBoxCurrentMeasure_parityAvoid_eq_freeIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxCurrentParity.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_parityAvoid_eq_freeIntegral_eq
  {d n : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 ≤ beta)
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  (freeBoxCurrentMeasure d (n + 1) beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder F) = ENNReal.ofReal ((∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(freeMeasure d (n + 1) beta 0 : Measure (ConfigSpace (Site d)))) * Real.cosh beta ^ F.card) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_parityAvoid_eq_freeIntegral d n beta hbeta F hF


-- created on 2026-10-23
