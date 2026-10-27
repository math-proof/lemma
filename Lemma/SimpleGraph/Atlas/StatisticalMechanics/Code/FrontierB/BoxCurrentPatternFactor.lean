import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentPatternFactor.Part2
open MeasureTheory Filter Topology StatMech StatMech.FrontierB


/--
[restrictCurrent_extendBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma restrictCurrent_extendBoxCurrent_eq
  {d n : ℕ}
  {F : Finset (Sym2 (Site d))}
  {m : EdgeCurrent (StatMech.FK.boxGraph d (n + 1))}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  restrictCurrent F (extendBoxCurrent d (n + 1) m) = pushforwardBoxLocalCurrent d n F hF (restrictCurrent (boxPullbackEdgeSubtypes d n F) m) := by
-- proof
  apply StatMech.FrontierB.restrictCurrent_extendBoxCurrent d n F hF m

/--
[finiteParityKernel_pullbackCurrentPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma finiteParityKernel_pullbackCurrentPattern_eq
  {d n : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
  {a : ↑F → ℕ}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  finiteParityKernel (boxPullbackEdgeSubtypes d n F) beta (currentLocalParity (pullbackCurrentPattern d n F hF a)) (pullbackCurrentPattern d n F hF a) = finiteParityKernel F beta (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.finiteParityKernel_pullbackCurrentPattern d n beta F hF a

/--
[preimage_currentCylinder_singleton_extendBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma preimage_currentCylinder_singleton_extendBoxCurrent_eq
  {d n : ℕ}
  {F : Finset (Sym2 (Site d))}
  {a : ↑F → ℕ}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  extendBoxCurrent d (n + 1) ⁻¹' currentCylinder F {a} = {m | restrictCurrent (boxPullbackEdgeSubtypes d n F) m = pullbackCurrentPattern d n F hF a} := by
-- proof
  apply StatMech.FrontierB.preimage_currentCylinder_singleton_extendBoxCurrent d n F hF a

/--
[currentLocalParity_restrictCurrent_eq_restrictParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma currentLocalParity_restrictCurrent_eq_restrictParity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset G.edgeFinset}
  {m : EdgeCurrent G} :
-- imply
  currentLocalParity (restrictCurrent S m) = restrictParity G S (currentParitySupport G m) := by
-- proof
  apply StatMech.FrontierB.currentLocalParity_restrictCurrent_eq_restrictParity G S m

/--
[boundaryCurrentLocalParityPMF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma boundaryCurrentLocalParityPMF_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta) :
-- imply
  PMF.map currentLocalParity (PMF.map (restrictCurrent S) (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) interior)) = PMF.map (restrictParity G S) (boundaryParityPMF G beta hbeta.le interior) := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentLocalParityPMF G beta hbeta interior S

/--
[sourcelessCurrentLocalParityPMF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma sourcelessCurrentLocalParityPMF_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta) :
-- imply
  PMF.map currentLocalParity (PMF.map (restrictCurrent S) (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one))) = PMF.map (restrictParity G S) (freeParityPMF G beta hbeta.le) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentLocalParityPMF G beta hbeta S

/--
[currentLocalParity_pushforward_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma currentLocalParity_pushforward_iff_eq
  {d n : ℕ}
  {F : Finset (Sym2 (Site d))}
  {a : ↑(boxPullbackEdgeSubtypes d n F) → ℕ}
  {odd : ↑F → Bool}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  currentLocalParity (pushforwardBoxLocalCurrent d n F hF a) = odd ↔ currentLocalParity a = pullbackParityPattern d n F hF odd := by
-- proof
  apply StatMech.FrontierB.currentLocalParity_pushforward_iff d n F hF a odd

/--
[preimage_currentParityPatternCylinder_extendBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma preimage_currentParityPatternCylinder_extendBoxCurrent_eq
  {d n : ℕ}
  {F : Finset (Sym2 (Site d))}
  {odd : ↑F → Bool}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  extendBoxCurrent d (n + 1) ⁻¹' currentParityPatternCylinder F odd = {m | currentLocalParity (restrictCurrent (boxPullbackEdgeSubtypes d n F) m) = pullbackParityPattern d n F hF odd} := by
-- proof
  apply StatMech.FrontierB.preimage_currentParityPatternCylinder_extendBoxCurrent d n F hF odd

/--
[plusBoxCurrentMeasure_pattern_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_pattern_factor_eq
  {d n : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
  {a : ↑F → ℕ}
-- given
  (hbeta : 0 < beta)
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  (plusBoxCurrentMeasure d (n + 1) beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder F {a}) = (plusBoxCurrentMeasure d (n + 1) beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityPatternCylinder F (currentLocalParity a)) * finiteParityPMF F beta hbeta (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_pattern_factor d n beta hbeta F hF a

/--
[freeBoxCurrentMeasure_pattern_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_pattern_factor_eq
  {d n : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
  {a : ↑F → ℕ}
-- given
  (hbeta : 0 < beta)
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  (freeBoxCurrentMeasure d (n + 1) beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder F {a}) = (freeBoxCurrentMeasure d (n + 1) beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityPatternCylinder F (currentLocalParity a)) * finiteParityPMF F beta hbeta (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_pattern_factor d n beta hbeta F hF a


-- created on 2026-10-23
