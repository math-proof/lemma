import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[forceOpenFinset_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma forceOpenFinset_of_mem_eq
  [Countable V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (he : e ∈ F) :
-- imply
  forceOpenFinset F omega e = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.forceOpenFinset_of_mem he omega

/--
[forceOpenFinset_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma forceOpenFinset_of_notMem_eq
  [Countable V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {e : Sym2 V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ F) :
-- imply
  forceOpenFinset F omega e = omega e := by
-- proof
  apply StatMech.FK.PeriodicPlanar.forceOpenFinset_of_notMem he omega

/--
[forceOpenFinset_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma forceOpenFinset_le_eq
  [Countable V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  omega <= forceOpenFinset F omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.forceOpenFinset_le F omega

/--
[PeriodicGraph.openSubgraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma openSubgraph_mono_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega eta : ConfigSpace (Sym2 V)}
-- given
  (h : omega <= eta) :
-- imply
  P.openSubgraph omega <= P.openSubgraph eta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.openSubgraph_mono P h

/--
[PeriodicGraph.reachable_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma reachable_mono_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega eta : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (h : omega <= eta)
  (hxy : (P.openSubgraph omega).Reachable x y) :
-- imply
  (P.openSubgraph eta).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.reachable_mono P h hxy

/--
[PeriodicGraph.cluster_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma cluster_mono_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega eta : ConfigSpace (Sym2 V)}
  {x : V}
-- given
  (h : omega <= eta) :
-- imply
  P.cluster omega x ⊆ P.cluster eta x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.cluster_mono P h x

/--
[encard_image_lt_of_not_injOn_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma encard_image_lt_of_not_injOn_periodic_eq
  [Countable V]
  [DecidableEq V]
  {s : Set A}
  {f : A -> B}
-- given
  (hfin : s.Finite)
  (hni : ¬ Set.InjOn f s) :
-- imply
  (f '' s).encard < s.encard := by
-- proof
  apply StatMech.FK.PeriodicPlanar.encard_image_lt_of_not_injOn_periodic hfin hni

/--
[finiteOpenAnchors_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma finiteOpenAnchors_finite_eq
  [Countable V]
  [DecidableEq V]
  {F : Finset (Sym2 V)} :
-- imply
  (finiteOpenAnchors F).Finite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finiteOpenAnchors_finite F

/--
[PeriodicGraph.adj_forceOpenFinset_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma adj_forceOpenFinset_cases_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {F : Finset (Sym2 V)}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (h : (P.openSubgraph (forceOpenFinset F omega)).Adj x y) :
-- imply
  (P.openSubgraph omega).Adj x y ∨ s(x, y) ∈ F := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.adj_forceOpenFinset_cases P F omega h

/--
[PeriodicGraph.forceOpen_reachable_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma forceOpen_reachable_anchor_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {F : Finset (Sym2 V)}
  {omega : ConfigSpace (Sym2 V)}
  {x z : V}
-- given
  (h : (P.openSubgraph (forceOpenFinset F omega)).Reachable x z) :
-- imply
  (P.openSubgraph omega).Reachable x z ∨ ∃ a ∈ finiteOpenAnchors F, (P.openSubgraph omega).Reachable a z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.forceOpen_reachable_anchor P F omega x z h

/--
[PeriodicGraph.exists_old_infinite_cluster_in_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma exists_old_infinite_cluster_in_forceOpen_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {F : Finset (Sym2 V)}
  {omega : ConfigSpace (Sym2 V)}
  {x : V}
-- given
  (hinf : (P.cluster (forceOpenFinset F omega) x).Infinite) :
-- imply
  ∃ a, a ∈ P.cluster (forceOpenFinset F omega) x ∧ (P.cluster omega a).Infinite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_old_infinite_cluster_in_forceOpen P F omega x hinf

/--
[PeriodicGraph.forceOpen_image_repSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma forceOpen_image_repSet_eq_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {F : Finset (Sym2 V)}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  (fun a => P.cluster (forceOpenFinset F omega) a) '' P.infiniteClusterRepSet omega = P.infiniteClusters (forceOpenFinset F omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.forceOpen_image_repSet_eq P F omega

/--
[PeriodicGraph.numInfiniteClusters_lt_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma numInfiniteClusters_lt_of_merge_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {F : Finset (Sym2 V)}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (hfin : P.numInfiniteClusters omega ≠ ⊤)
  (hx : (P.cluster omega x).Infinite)
  (hy : (P.cluster omega y).Infinite)
  (hne : P.cluster omega x ≠ P.cluster omega y)
  (hmerge : (P.openSubgraph (forceOpenFinset F omega)).Reachable x y) :
-- imply
  P.numInfiniteClusters (forceOpenFinset F omega) < P.numInfiniteClusters omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_lt_of_merge P F omega hfin x y hx hy hne hmerge

/--
[PeriodicGraph.exists_distinctInfinitePair_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma exists_distinctInfinitePair_of_two_le_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (h : 2 <= P.numInfiniteClusters omega) :
-- imply
  ∃ x y, omega ∈ P.distinctInfinitePairEvent x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_distinctInfinitePair_of_two_le P h

/--
[PeriodicGraph.exists_distinctInfinitePair_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma exists_distinctInfinitePair_pos_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {k : ℕ∞}
-- given
  (hk : mu {omega | P.numInfiniteClusters omega = k} = 1)
  (hk2 : 2 <= k) :
-- imply
  ∃ x y, 0 < mu (P.distinctInfinitePairEvent x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_distinctInfinitePair_pos P mu hk hk2

/--
[PeriodicGraph.exists_forceOpen_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma exists_forceOpen_walk_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {x y : V}
-- given
  (hconn : P.graph.Connected) :
-- imply
  ∃ F : Finset (Sym2 V), ∀ omega, (P.openSubgraph (forceOpenFinset F omega)).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_forceOpen_walk P hconn x y

/--
[PeriodicGraph.measurableSet_numInfiniteClusters_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma measurableSet_numInfiniteClusters_lt_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {k : ℕ∞} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | P.numInfiniteClusters omega < k} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_numInfiniteClusters_lt P k

/--
[PeriodicGraph.numInfiniteClusters_lt_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma numInfiniteClusters_lt_null_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {k : ℕ∞}
-- given
  (hk : mu {omega | P.numInfiniteClusters omega = k} = 1) :
-- imply
  mu {omega | P.numInfiniteClusters omega < k} = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_lt_null P mu hk

/--
[PeriodicGraph.numInfiniteClusters_const_ne_finite_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma numInfiniteClusters_const_ne_finite_two_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {k : ℕ∞}
-- given
  (hconn : P.graph.Connected)
  (hfe : HasFiniteEnergy mu)
  (hk : mu {omega | P.numInfiniteClusters omega = k} = 1)
  (hk2 : 2 <= k)
  (hktop : k ≠ ⊤) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_const_ne_finite_two P hconn mu hfe hk hk2 hktop

/--
[PeriodicGraph.numInfiniteClusters_zero_one_or_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean)
-/
@[path]
private lemma numInfiniteClusters_zero_one_or_top_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hconn : P.graph.Connected)
  (herg : P.IsErgodic mu)
  (hfe : HasFiniteEnergy mu) :
-- imply
  ∃ k : ℕ∞, mu {omega | P.numInfiniteClusters omega = k} = 1 ∧ (k = 0 ∨ k = 1 ∨ k = ⊤) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_zero_one_or_top P hconn mu herg hfe


-- created on 2026-10-23
