import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail.Part3
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.infiniteCluster_component_after_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean)
-/
@[path]
private lemma infiniteCluster_component_after_finset_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x : V}
  {K : Finset V}
-- given
  (hinf : (P.cluster omega x).Infinite) :
-- imply
  ∃ D : (P.tailClusterGraph omega x).ComponentCompl (P.tailClusterCut omega x K), D.supp.Infinite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteCluster_component_after_finset P omega x hinf K

/--
[PeriodicGraph.tailComponentVertices_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean)
-/
@[path]
private lemma tailComponentVertices_infinite_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x : V}
  {K : Finset V}
  {D : (P.tailClusterGraph omega x).ComponentCompl (P.tailClusterCut omega x K)}
-- given
  (hD : D.supp.Infinite) :
-- imply
  (P.tailComponentVertices omega x K D).Infinite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.tailComponentVertices_infinite P omega x K D hD

/--
[PeriodicGraph.tailComponentVertices_subset_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean)
-/
@[path]
private lemma tailComponentVertices_subset_cluster_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x : V}
  {K : Finset V}
  {D : (P.tailClusterGraph omega x).ComponentCompl (P.tailClusterCut omega x K)} :
-- imply
  P.tailComponentVertices omega x K D ⊆ P.cluster omega x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.tailComponentVertices_subset_cluster P omega x K D

/--
[PeriodicGraph.tailComponentVertices_connected_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean)
-/
@[path]
private lemma tailComponentVertices_connected_outside_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x : V}
  {K : Finset V}
  {D : (P.tailClusterGraph omega x).ComponentCompl (P.tailClusterCut omega x K)} :
-- imply
  ∀ u ∈ P.tailComponentVertices omega x K D, ∀ v ∈ P.tailComponentVertices omega x K D, ∃ (hu : u ∉ (K : Set V)) (hv : v ∉ (K : Set V)), ((P.openSubgraph omega).induce (K : Set V)ᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.tailComponentVertices_connected_outside P omega x K D

/--
[PeriodicGraph.infiniteCluster_has_open_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean)
-/
@[path]
private lemma infiniteCluster_has_open_exit_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x : V}
  {K : Finset V}
-- given
  (hinf : (P.cluster omega x).Infinite)
  (hxK : x ∈ K) :
-- imply
  Nonempty (P.InfiniteTailData omega K x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteCluster_has_open_exit P omega x hinf K hxK


-- created on 2026-10-23
