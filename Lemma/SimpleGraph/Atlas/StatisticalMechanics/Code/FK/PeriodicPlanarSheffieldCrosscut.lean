import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrosscut
open Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicPlaneEmbedding.simpleWalkArc_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma simpleWalkArc_nil_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x : V} :
-- imply
  E.simpleWalkArc (.nil : P.graph.Walk x x) = Path.refl _ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.simpleWalkArc_nil E x

/--
[PeriodicPlaneEmbedding.simpleWalkArc_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma simpleWalkArc_single_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x y : V}
-- given
  (hxy : P.graph.Adj x y) :
-- imply
  E.simpleWalkArc (.cons hxy .nil) = E.edgeArc hxy := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.simpleWalkArc_single E hxy

/--
[PeriodicPlaneEmbedding.simpleWalkArc_cons_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma simpleWalkArc_cons_cons_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x y z w : V}
  {p : P.graph.Walk z w}
-- given
  (hxy : P.graph.Adj x y)
  (hyz : P.graph.Adj y z) :
-- imply
  E.simpleWalkArc (.cons hxy (.cons hyz p)) = (E.edgeArc hxy).trans (E.simpleWalkArc (.cons hyz p)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.simpleWalkArc_cons_cons E hxy hyz p

/--
[PeriodicPlaneEmbedding.simpleWalkArc_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma simpleWalkArc_range_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x y : V}
  {p : P.graph.Walk x y} :
-- imply
  Set.range (E.simpleWalkArc p) = Set.range (E.walkArc p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.simpleWalkArc_range E p

/--
[PeriodicPlaneEmbedding.edgeArc_inter_simpleWalkArc_eq_join](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma edgeArc_inter_simpleWalkArc_eq_join_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x y z : V}
  {p : P.graph.Walk y z}
  {q : ℂ}
-- given
  (hxy : P.graph.Adj x y)
  (hpath : (p.cons hxy).IsPath)
  (hqEdge : q ∈ Set.range (E.edgeArc hxy))
  (hqRest : q ∈ Set.range (E.simpleWalkArc p)) :
-- imply
  q = E.vertex y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.edgeArc_inter_simpleWalkArc_eq_join E hxy p hpath hqEdge hqRest

/--
[pathTrans_injective_of_range_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma pathTrans_injective_of_range_inter_eq
  [DecidableEq V]
  [Countable V]
  [TopologicalSpace X]
  {x y z : X}
  {gamma : Path x y}
  {eta : Path y z}
-- given
  (hgamma : Function.Injective gamma)
  (heta : Function.Injective eta)
  (hinter : ∀ q, q ∈ Set.range gamma → q ∈ Set.range eta → q = y) :
-- imply
  Function.Injective (gamma.trans eta) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.pathTrans_injective_of_range_inter gamma eta hgamma heta hinter

/--
[PeriodicPlaneEmbedding.simpleWalkArc_injective_of_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma simpleWalkArc_injective_of_isPath_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x y : V}
  {p : P.graph.Walk x y}
-- given
  (hp : p.IsPath)
  (hnil : ¬ p.Nil) :
-- imply
  Function.Injective (E.simpleWalkArc p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.simpleWalkArc_injective_of_isPath E p hp hnil

/--
[PeriodicPlaneEmbedding.exists_injective_walkArc_toPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma exists_injective_walkArc_toPath_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x y : V}
  {p : P.graph.Walk x y}
-- given
  (hxy : x ≠ y) :
-- imply
  Function.Injective (E.simpleWalkArc (p.toPath : P.graph.Walk x y)) ∧ (p.toPath : P.graph.Walk x y).edges ⊆ p.edges := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_injective_walkArc_toPath E p hxy

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_simpleCrosscut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_simpleCrosscut_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (hcd : c < d)
  (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ q : P.graph.Walk b u, q.IsPath ∧ ¬ q.Nil ∧ Function.Injective (E.simpleWalkArc q) ∧ (∀ {x y : V}, s(x, y) ∈ q.edges → omega s(x, y) = true) ∧ ∀ v ∈ q.support, v ∈ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_simpleCrosscut E hcd h

/--
[no_open_primal_dual_simpleWalkArc_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCrosscut.lean)
-/
@[path]
private lemma no_open_primal_dual_simpleWalkArc_crossing_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
  {a b : W}
  {p : P.graph.Walk x y}
  {q : Pdual.graph.Walk a b}
-- given
  (hp : ¬ p.Nil)
  (hq : ¬ q.Nil)
  (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges → omega s(u, v) = true)
  (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges → dualConfigEquiv D.edgeDual omega s(u, v) = true) :
-- imply
  Disjoint (Set.range (D.primalEmbedding.simpleWalkArc p)) (Set.range (D.dualEmbedding.simpleWalkArc q)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_open_primal_dual_simpleWalkArc_crossing D omega p q hp hq hpopen hqopen


-- created on 2026-10-23
