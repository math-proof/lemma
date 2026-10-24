import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeanePattern
open MeasureTheory Set SimpleGraph Finset StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.mem_incidentEdgeFinset_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeanePattern.lean)
-/
@[path]
private lemma mem_incidentEdgeFinset_mk_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {K : Finset V}
  {x y : V} :
-- imply
  s(x, y) ∈ P.incidentEdgeFinset K ↔ P.graph.Adj x y ∧ (x ∈ K ∨ y ∈ K) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.mem_incidentEdgeFinset_mk P K x y

/--
[PeriodicGraph.exteriorOpenGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeanePattern.lean)
-/
@[path]
private lemma exteriorOpenGraph_le_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {K : Finset V} :
-- imply
  P.exteriorOpenGraph omega K ≤ P.openSubgraph omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exteriorOpenGraph_le P omega K

/--
[PeriodicGraph.three_clusters_core_pattern_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeanePattern.lean)
-/
@[path]
private lemma three_clusters_core_pattern_trifurcation_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {K : Finset V}
  {x : Fin 3 → V}
-- given
  (hKconn : (P.graph.induce (K : Set V)).Connected)
  (hxK : ∀ i, x i ∈ K)
  (hinf : ∀ i, (P.cluster omega (x i)).Infinite)
  (hclusters : ∀ i j, i ≠ j → P.cluster omega (x i) ≠ P.cluster omega (x j)) :
-- imply
  ∃ (eta : ConfigSpace ↥(P.incidentEdgeFinset K)) (hub : V), P.IsTrifurcation (setPattern (P.incidentEdgeFinset K) eta omega) hub := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.three_clusters_core_pattern_trifurcation P omega K hKconn x hxK hinf hclusters

/--
[PeriodicGraph.three_clusters_pattern_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeanePattern.lean)
-/
@[path]
private lemma three_clusters_pattern_trifurcation_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x : Fin 3 → V}
-- given
  (hconn : P.graph.Connected)
  (hinf : ∀ i, (P.cluster omega (x i)).Infinite)
  (hclusters : ∀ i j, i ≠ j → P.cluster omega (x i) ≠ P.cluster omega (x j)) :
-- imply
  ∃ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (hub : V), P.IsTrifurcation (setPattern I eta omega) hub := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.three_clusters_pattern_trifurcation P hconn omega x hinf hclusters


-- created on 2026-10-23
