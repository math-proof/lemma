import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentTraceZeroBeta
open Filter MeasureTheory StatMech StatMech.FrontierB


/--
[weight_zero_beta_of_edgeCurrent_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma weight_zero_beta_of_edgeCurrent_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : EdgeCurrent G}
-- given
  (J : Sym2 V -> Real)
  (hm : m ≠ 0) :
-- imply
  weight G 0 J (ofEdgeFun G m) = 0 := by
-- proof
  apply StatMech.FrontierB.weight_zero_beta_of_edgeCurrent_ne_zero G J m hm

/--
[sourcelessCurrentPMF_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma sourcelessCurrentPMF_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  sourcelessCurrentPMF G 0 J le_rfl hJ = PMF.pure 0 := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentPMF_zero_beta G J hJ

/--
[boundaryCurrentPMF_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma boundaryCurrentPMF_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {interior : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  boundaryCurrentPMF G 0 J le_rfl hJ interior = PMF.pure 0 := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentPMF_zero_beta G J hJ interior

/--
[extendBoxCurrent_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma extendBoxCurrent_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat} :
-- imply
  extendBoxCurrent d n (0 : EdgeCurrent (StatMech.FK.boxGraph d n)) = 0 := by
-- proof
  apply StatMech.FrontierB.extendBoxCurrent_zero G d n

/--
[freeBoxCurrentMeasure_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat} :
-- imply
  (freeBoxCurrentMeasure d n 0 le_rfl : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) = Measure.dirac 0 := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_zero_beta G d n

/--
[plusBoxCurrentMeasure_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat} :
-- imply
  (plusBoxCurrentMeasure d n 0 le_rfl : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) = Measure.dirac 0 := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_zero_beta G d n

/--
[infiniteFreeCurrentMeasure_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma infiniteFreeCurrentMeasure_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  (infiniteFreeCurrentMeasure d 0 le_rfl : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) = Measure.dirac 0 := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentMeasure_zero_beta G d

/--
[infinitePlusCurrentMeasure_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma infinitePlusCurrentMeasure_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  (infinitePlusCurrentMeasure d 0 le_rfl : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) = Measure.dirac 0 := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentMeasure_zero_beta G d

/--
[independentSuperposedTraceLaw_eq_dirac_allClosed_of_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma independentSuperposedTraceLaw_eq_dirac_allClosed_of_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Countable E]
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (hmu : (mu : Measure (InfiniteCurrentConfig E)) = Measure.dirac 0)
  (hnu : (nu : Measure (InfiniteCurrentConfig E)) = Measure.dirac 0) :
-- imply
  (independentSuperposedTraceLaw mu nu : Measure (ConfigSpace E)) = Measure.dirac (fun _ => false) := by
-- proof
  apply StatMech.FrontierB.independentSuperposedTraceLaw_eq_dirac_allClosed_of_eq_zero G mu nu hmu hnu

/--
[freeFreeSuperposedTraceLaw_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma freeFreeSuperposedTraceLaw_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d 0 le_rfl) (infiniteFreeCurrentMeasure d 0 le_rfl) : Measure (ConfigSpace (Sym2 (Site d)))) = Measure.dirac (fun _ => false) := by
-- proof
  apply StatMech.FrontierB.freeFreeSuperposedTraceLaw_zero_beta G d

/--
[freePlusSuperposedTraceLaw_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d 0 le_rfl) (infinitePlusCurrentMeasure d 0 le_rfl) : Measure (ConfigSpace (Sym2 (Site d)))) = Measure.dirac (fun _ => false) := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_zero_beta G d

/--
[plusPlusSuperposedTraceLaw_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma plusPlusSuperposedTraceLaw_zero_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d 0 le_rfl) (infinitePlusCurrentMeasure d 0 le_rfl) : Measure (ConfigSpace (Sym2 (Site d)))) = Measure.dirac (fun _ => false) := by
-- proof
  apply StatMech.FrontierB.plusPlusSuperposedTraceLaw_zero_beta G d

/--
[openSubgraph_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma openSubgraph_allClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  openSubgraph d (fun _ => false) = ⊥ := by
-- proof
  apply StatMech.FrontierB.openSubgraph_allClosed G d

/--
[cluster_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma cluster_allClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {x : Site d} :
-- imply
  cluster d (fun _ => false) x = {x} := by
-- proof
  apply StatMech.FrontierB.cluster_allClosed G d x

/--
[numInfiniteClusters_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma numInfiniteClusters_allClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  numInfiniteClusters d (fun _ => false) = 0 := by
-- proof
  apply StatMech.FrontierB.numInfiniteClusters_allClosed G d

/--
[dirac_allClosed_cluster_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma dirac_allClosed_cluster_uniqueness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  let mu := Measure.dirac (fun _ => false : ConfigSpace (Sym2 (Site d))) (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨ mu {omega | numInfiniteClusters d omega = 1} = 1) ∧ mu (atLeastTwoInfinite d) = 0 ∧ mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.dirac_allClosed_cluster_uniqueness G d

/--
[freeFreeSuperposedTraceLaw_zero_beta_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma freeFreeSuperposedTraceLaw_zero_beta_uniqueness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  let mu := (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d 0 le_rfl) (infiniteFreeCurrentMeasure d 0 le_rfl) : Measure (ConfigSpace (Sym2 (Site d)))) (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨ mu {omega | numInfiniteClusters d omega = 1} = 1) ∧ mu (atLeastTwoInfinite d) = 0 ∧ mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.freeFreeSuperposedTraceLaw_zero_beta_uniqueness G d

/--
[freePlusSuperposedTraceLaw_zero_beta_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_zero_beta_uniqueness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  let mu := (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d 0 le_rfl) (infinitePlusCurrentMeasure d 0 le_rfl) : Measure (ConfigSpace (Sym2 (Site d)))) (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨ mu {omega | numInfiniteClusters d omega = 1} = 1) ∧ mu (atLeastTwoInfinite d) = 0 ∧ mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_zero_beta_uniqueness G d

/--
[plusPlusSuperposedTraceLaw_zero_beta_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceZeroBeta.lean)
-/
@[path]
private lemma plusPlusSuperposedTraceLaw_zero_beta_uniqueness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat} :
-- imply
  let mu := (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d 0 le_rfl) (infinitePlusCurrentMeasure d 0 le_rfl) : Measure (ConfigSpace (Sym2 (Site d)))) (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨ mu {omega | numInfiniteClusters d omega = 1} = 1) ∧ mu (atLeastTwoInfinite d) = 0 ∧ mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.plusPlusSuperposedTraceLaw_zero_beta_uniqueness G d


-- created on 2026-10-23
