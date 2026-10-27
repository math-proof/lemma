import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneCore.Part3
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[periodicVertexIndex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma periodicVertexIndex_injective_eq
  [Countable V]
  [DecidableEq V] :
-- imply
  Function.Injective (periodicVertexIndex V) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.periodicVertexIndex_injective

/--
[PeriodicGraph.self_mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma self_mem_cluster_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x : V} :
-- imply
  x ∈ P.cluster omega x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.self_mem_cluster P omega x

/--
[PeriodicGraph.cluster_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma cluster_eq_of_reachable_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (hxy : (P.openSubgraph omega).Reachable x y) :
-- imply
  P.cluster omega x = P.cluster omega y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.cluster_eq_of_reachable P omega hxy

/--
[PeriodicGraph.infiniteClusters_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma infiniteClusters_configTranslate_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.infiniteClusters (P.configTranslate z omega) = (fun C : Set V => P.shift z '' C) '' P.infiniteClusters omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteClusters_configTranslate P z omega

/--
[PeriodicGraph.numInfiniteClusters_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma numInfiniteClusters_configTranslate_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.numInfiniteClusters (P.configTranslate z omega) = P.numInfiniteClusters omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_configTranslate P z omega

/--
[exists_periodicVertexIndex_min](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma exists_periodicVertexIndex_min_eq
  [Countable V]
  [DecidableEq V]
  {S : Set V}
-- given
  (hne : S.Nonempty) :
-- imply
  ∃ x ∈ S, ∀ y ∈ S, periodicVertexIndex V x <= periodicVertexIndex V y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_periodicVertexIndex_min S hne

/--
[PeriodicGraph.image_cluster_infiniteClusterRepSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma image_cluster_infiniteClusterRepSet_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  (fun x => P.cluster omega x) '' P.infiniteClusterRepSet omega = P.infiniteClusters omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.image_cluster_infiniteClusterRepSet P omega

/--
[PeriodicGraph.injOn_cluster_infiniteClusterRepSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma injOn_cluster_infiniteClusterRepSet_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  Set.InjOn (fun x => P.cluster omega x) (P.infiniteClusterRepSet omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.injOn_cluster_infiniteClusterRepSet P omega

/--
[PeriodicGraph.numInfiniteClusters_eq_repSet_encard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma numInfiniteClusters_eq_repSet_encard_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.numInfiniteClusters omega = (P.infiniteClusterRepSet omega).encard := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_eq_repSet_encard P omega

/--
[PeriodicGraph.measurableSet_infiniteClusterRepSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma measurableSet_infiniteClusterRepSet_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {x : V} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | x ∈ P.infiniteClusterRepSet omega} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_infiniteClusterRepSet P x

/--
[PeriodicGraph.measurable_numInfiniteClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma measurable_numInfiniteClusters_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  Measurable P.numInfiniteClusters := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurable_numInfiniteClusters P

/--
[PeriodicGraph.numInfiniteClusters_eq_one_iff_hasUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma numInfiniteClusters_eq_one_iff_hasUnique_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.numInfiniteClusters omega = 1 ↔ P.HasUniqueInfiniteCluster omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_eq_one_iff_hasUnique P omega

/--
[PeriodicGraph.numInfiniteClusters_eq_one_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma numInfiniteClusters_eq_one_event_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  {omega : ConfigSpace (Sym2 V) | P.numInfiniteClusters omega = 1} = {omega | P.HasUniqueInfiniteCluster omega} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_eq_one_event P

/--
[PeriodicGraph.numInfiniteClusters_ae_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean)
-/
@[path]
private lemma numInfiniteClusters_ae_const_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (herg : P.IsErgodic mu) :
-- imply
  ∃ k : ℕ∞, mu {omega | P.numInfiniteClusters omega = k} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_ae_const P mu herg


-- created on 2026-10-23
