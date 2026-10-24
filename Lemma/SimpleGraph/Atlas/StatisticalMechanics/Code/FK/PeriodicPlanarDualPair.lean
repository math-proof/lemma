import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[period_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma period_eq_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual} :
-- imply
  D.primalEmbedding.period = D.dualEmbedding.period := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.period_eq D

/--
[swap_primalEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma swap_primalEmbedding_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual} :
-- imply
  D.swap.primalEmbedding = D.dualEmbedding := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.swap_primalEmbedding D

/--
[swap_dualEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma swap_dualEmbedding_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual} :
-- imply
  D.swap.dualEmbedding = D.primalEmbedding := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.swap_dualEmbedding D

/--
[PeriodicPlaneEmbedding.shift_ne_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma shift_ne_of_ne_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {x : V}
-- given
  (hz : z ≠ 0) :
-- imply
  P.shift z x ≠ x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.PeriodicPlaneEmbedding.shift_ne_of_ne E hz x

/--
[PeriodicGraph.orbitBox_card_le_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma orbitBox_card_le_quadratic_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  (P.orbitBox n).card ≤ (2 * n + 1) ^ 2 * P.fundamentalDomain.card := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.PeriodicGraph.orbitBox_card_le_quadratic P n

/--
[probabilityMeasure_eq_of_finiteCylinder_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma probabilityMeasure_eq_of_finiteCylinder_real_eq_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  [Countable E]
  {mu nu : ProbabilityMeasure (ConfigSpace E)}
-- given
  (h : ∀ (s : Finset E) (S : Set (∀ _i : s, Bool)), (mu : Measure (ConfigSpace E)).real (cylinder s S) = (nu : Measure (ConfigSpace E)).real (cylinder s S)) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.probabilityMeasure_eq_of_finiteCylinder_real_eq mu nu h

/--
[free_wired_infiniteVolume_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma free_wired_infiniteVolume_dual_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Pdual.wiredBufferedInfiniteVolume (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1 (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2 (zero_lt_one.trans_le hq) = (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)).map (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.free_wired_infiniteVolume_dual D hp hp1 hq

/--
[wired_free_infiniteVolume_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma wired_free_infiniteVolume_dual_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Pdual.freeBufferedInfiniteVolume (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1 (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2 (zero_lt_one.trans_le hq) = (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)).map (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.wired_free_infiniteVolume_dual D hp hp1 hq

/--
[percolationEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma percolationEvent_measurableSet_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V} :
-- imply
  MeasurableSet P.percolationEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.percolationEvent_measurableSet P

/--
[wiredDual_percolationEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma wiredDual_percolationEvent_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  ((Pdual.wiredBufferedInfiniteVolume (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1 (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 W))) : Measure (ConfigSpace (Sym2 W))) Pdual.percolationEvent = ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) ((dualConfigEquiv D.edgeDual) ⁻¹' Pdual.percolationEvent) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.wiredDual_percolationEvent D hp hp1 hq

/--
[wiredPercolationProbability_dualParam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma wiredPercolationProbability_dualParam_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Pdual.wiredPercolationProbability (dualParam p q) q = D.freeDualPercolationProbability p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.wiredPercolationProbability_dualParam D hp hp1 hq

/--
[wiredPercolates_dualParam_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma wiredPercolates_dualParam_iff_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Pdual.wiredPercolates (dualParam p q) q ↔ D.FreeDualPercolates p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.wiredPercolates_dualParam_iff D hp hp1 hq

/--
[dualSubcriticalCoverage_iff_freeDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma dualSubcriticalCoverage_iff_freeDual_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {pc q : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  DualSubcriticalCoverage (fun r => Pdual.wiredPercolates r q) pc q ↔ ∀ p ∈ Ioo (0 : ℝ) 1, p < pc → D.FreeDualPercolates p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualSubcriticalCoverage_iff_freeDual D hq

/--
[dualNoCoexistence_iff_freeDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma dualNoCoexistence_iff_freeDual_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  DualNoCoexistence (fun p => P.wiredPercolates p q) (fun r => Pdual.wiredPercolates r q) q ↔ ∀ p ∈ Ioo (0 : ℝ) 1, ¬(P.wiredPercolates p q ∧ D.FreeDualPercolates p q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualNoCoexistence_iff_freeDual D hq

/--
[dualCritical_relation_of_commonCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean)
-/
@[path]
private lemma dualCritical_relation_of_commonCoupling_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : ℝ}
-- given
  (hpc : P.criticalPoint q ∈ Ioo (0 : ℝ) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : ℝ) 1)
  (hq : 1 ≤ q)
  (hcoverage : ∀ p ∈ Ioo (0 : ℝ) 1, p < P.criticalPoint q → D.FreeDualPercolates p q)
  (hnoCoexistence : ∀ p ∈ Ioo (0 : ℝ) 1, ¬(P.wiredPercolates p q ∧ D.FreeDualPercolates p q)) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_commonCoupling D hpc hpcDual hq hcoverage hnoCoexistence


-- created on 2026-10-23
