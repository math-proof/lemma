import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.openSubgraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma openSubgraph_adj_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V} :
-- imply
  (P.openSubgraph omega).Adj x y ↔ P.graph.Adj x y ∧ omega s(x, y) = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.openSubgraph_adj P omega x y

/--
[PeriodicGraph.root_mem_fundamentalDomain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma root_mem_fundamentalDomain_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V} :
-- imply
  P.root ∈ P.fundamentalDomain := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.root_mem_fundamentalDomain P

/--
[PeriodicGraph.wiredPercolationProbability_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma wiredPercolationProbability_nonneg_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ} :
-- imply
  0 ≤ P.wiredPercolationProbability p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredPercolationProbability_nonneg P p q

/--
[PeriodicGraph.wiredPercolationProbability_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma wiredPercolationProbability_le_one_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ} :
-- imply
  P.wiredPercolationProbability p q ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredPercolationProbability_le_one P p q

/--
[PeriodicGraph.mem_subcriticalSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma mem_subcriticalSet_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ} :
-- imply
  p ∈ P.subcriticalSet q ↔ p ∈ Ioo (0 : ℝ) 1 ∧ P.wiredPercolationProbability p q = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.mem_subcriticalSet P

/--
[dualParam_strictAntiOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma dualParam_strictAntiOn_eq
  [DecidableEq V]
  [DecidableEq W]
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  StrictAntiOn (fun p : ℝ ↦ dualParam p q) (Ioo 0 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualParam_strictAntiOn hq

/--
[dualCritical_crossBounds_of_sharpness_noCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma dualCritical_crossBounds_of_sharpness_noCoexistence_eq
  [DecidableEq V]
  [DecidableEq W]
  {primalPercolates dualPercolates : ℝ → Prop}
  {pc pcDual q : ℝ}
-- given
  (hq : 0 < q)
  (hsharpPrimal : OffCriticalSharpness primalPercolates pc)
  (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
  (hcoverage : DualSubcriticalCoverage dualPercolates pc q)
  (hnoCoexistence : DualNoCoexistence primalPercolates dualPercolates q) :
-- imply
  (∀ p ∈ Ioo (0 : ℝ) 1, p < pc → pcDual ≤ dualParam p q) ∧ (∀ p ∈ Ioo (0 : ℝ) 1, pc < p → dualParam p q ≤ pcDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualCritical_crossBounds_of_sharpness_noCoexistence hq hsharpPrimal hsharpDual hcoverage hnoCoexistence

/--
[dualCritical_eq_of_crossBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma dualCritical_eq_of_crossBounds_eq
  [DecidableEq V]
  [DecidableEq W]
  {pc pcDual q : ℝ}
-- given
  (hpc : pc ∈ Ioo (0 : ℝ) 1)
  (hpcDual : pcDual ∈ Ioo (0 : ℝ) 1)
  (hq : 0 < q)
  (hsub : ∀ p ∈ Ioo (0 : ℝ) 1, p < pc → pcDual ≤ dualParam p q)
  (hsuper : ∀ p ∈ Ioo (0 : ℝ) 1, pc < p → dualParam p q ≤ pcDual) :
-- imply
  dualParam pc q = pcDual := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualCritical_eq_of_crossBounds hpc hpcDual hq hsub hsuper

/--
[dualCritical_relation_of_sharpness_noCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma dualCritical_relation_of_sharpness_noCoexistence_eq
  [DecidableEq V]
  [DecidableEq W]
  {primalPercolates dualPercolates : ℝ → Prop}
  {pc pcDual q : ℝ}
-- given
  (hpc : pc ∈ Ioo (0 : ℝ) 1)
  (hpcDual : pcDual ∈ Ioo (0 : ℝ) 1)
  (hq : 0 < q)
  (hsharpPrimal : OffCriticalSharpness primalPercolates pc)
  (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
  (hcoverage : DualSubcriticalCoverage dualPercolates pc q)
  (hnoCoexistence : DualNoCoexistence primalPercolates dualPercolates q) :
-- imply
  dualParam pc q = pcDual ∧ (pc / (1 - pc)) * (pcDual / (1 - pcDual)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualCritical_relation_of_sharpness_noCoexistence hpc hpcDual hq hsharpPrimal hsharpDual hcoverage hnoCoexistence

/--
[PeriodicGraph.dualCritical_relation_of_sharpness_noCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean)
-/
@[path]
private lemma dualCritical_relation_of_sharpness_noCoexistence_eq_2
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {q : ℝ}
-- given
  (hpc : P.criticalPoint q ∈ Ioo (0 : ℝ) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : ℝ) 1)
  (hq : 0 < q)
  (hsharpPrimal : OffCriticalSharpness (fun p ↦ P.wiredPercolates p q) (P.criticalPoint q))
  (hsharpDual : OffCriticalSharpness (fun p ↦ Pdual.wiredPercolates p q) (Pdual.criticalPoint q))
  (hcoverage : DualSubcriticalCoverage (fun p ↦ Pdual.wiredPercolates p q) (P.criticalPoint q) q)
  (hnoCoexistence : DualNoCoexistence (fun p ↦ P.wiredPercolates p q) (fun p ↦ Pdual.wiredPercolates p q) q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.dualCritical_relation_of_sharpness_noCoexistence P Pdual hpc hpcDual hq hsharpPrimal hsharpDual hcoverage hnoCoexistence


-- created on 2026-10-23
