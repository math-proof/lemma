import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCrossingGluing.Part2
open Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.openSubgraphAmbientHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean)
-/
@[path]
private lemma openSubgraphAmbientHom_apply_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {v : V} :
-- imply
  P.openSubgraphAmbientHom omega v = v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.openSubgraphAmbientHom_apply P omega v

/--
[PeriodicPlaneEmbedding.openRectToOpenSubgraphHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean)
-/
@[path]
private lemma openRectToOpenSubgraphHom_apply_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ}
  {omega : ConfigSpace (Sym2 V)}
  {v : E.RectVertex a b c d} :
-- imply
  E.openRectToOpenSubgraphHom a b c d omega v = v.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.openRectToOpenSubgraphHom_apply E a b c d omega v

/--
[PeriodicPlaneEmbedding.map_openRectToOpenSubgraphHom_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean)
-/
@[path]
private lemma map_openRectToOpenSubgraphHom_ambient_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ}
  {omega : ConfigSpace (Sym2 V)}
  {x y : E.RectVertex a b c d}
  {p : (FK.openSub (E.rectGraph a b c d) (E.rectRestrict a b c d omega)).Walk x y} :
-- imply
  (p.map (E.openRectToOpenSubgraphHom a b c d omega)).map (P.openSubgraphAmbientHom omega) = p.map (E.openRectHom a b c d (E.rectRestrict a b c d omega)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.map_openRectToOpenSubgraphHom_ambient E a b c d omega p

/--
[PeriodicPlaneEmbedding.openSub_rectRestrict_eq_induce_gluing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean)
-/
@[path]
private lemma openSub_rectRestrict_eq_induce_gluing_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  FK.openSub (E.rectGraph a b c d) (E.rectRestrict a b c d omega) = (P.openSubgraph omega).induce (E.rectVertices a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.openSub_rectRestrict_eq_induce_gluing E a b c d omega

/--
[PeriodicPlaneEmbedding.exists_common_support_of_walkArc_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean)
-/
@[path]
private lemma exists_common_support_of_walkArc_intersection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x y z w : V}
  {p : P.graph.Walk x y}
  {q : P.graph.Walk z w}
  {r : ℂ}
-- given
  (hp : ¬ p.Nil)
  (hq : ¬ q.Nil)
  (hrp : r ∈ Set.range (E.walkArc p))
  (hrq : r ∈ Set.range (E.walkArc q)) :
-- imply
  ∃ v : V, v ∈ p.support ∧ v ∈ q.support := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_common_support_of_walkArc_intersection E p q hp hq hrp hrq

/--
[PeriodicPlaneEmbedding.openWalk_start_reachable_of_walkArc_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean)
-/
@[path]
private lemma openWalk_start_reachable_of_walkArc_intersection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {x y z w : V}
  {p : (P.openSubgraph omega).Walk x y}
  {q : (P.openSubgraph omega).Walk z w}
  {r : ℂ}
-- given
  (hxy : x ≠ y)
  (hzw : z ≠ w)
  (hrp : r ∈ Set.range (E.walkArc (p.map (P.openSubgraphAmbientHom omega))))
  (hrq : r ∈ Set.range (E.walkArc (q.map (P.openSubgraphAmbientHom omega)))) :
-- imply
  (P.openSubgraph omega).Reachable x z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.openWalk_start_reachable_of_walkArc_intersection E omega p q hxy hzw hrp hrq

/--
[PeriodicPlaneEmbedding.bufferedOpenRectWalks_start_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean)
-/
@[path]
private lemma bufferedOpenRectWalks_start_reachable_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B a b c d av bv : ℝ}
  {omega : ConfigSpace (Sym2 V)}
  {xp yp : E.RectVertex a b (c + 4 * B) (d - 4 * B)}
  {xd yd : E.RectVertex av bv c d}
  {p : (FK.openSub (E.rectGraph a b (c + 4 * B) (d - 4 * B)) (E.rectRestrict a b (c + 4 * B) (d - 4 * B) omega)).Walk xp yp}
  {q : (FK.openSub (E.rectGraph av bv c d) (E.rectRestrict av bv c d omega)).Walk xd yd}
-- given
  (hBpos : 0 < B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B)
  (hav : a + 3 * B < av)
  (hbv : bv + 3 * B < b)
  (hxp : E.rectLeftBoundary a b (c + 4 * B) (d - 4 * B) xp)
  (hyp : E.rectRightBoundary a b (c + 4 * B) (d - 4 * B) yp)
  (hxd : E.rectBottomBoundary av bv c d xd)
  (hyd : E.rectTopBoundary av bv c d yd) :
-- imply
  ∃ r : (P.openSubgraph omega).Walk xp.1 xd.1, ∀ v ∈ r.support, v ∈ E.rectVertices a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.bufferedOpenRectWalks_start_reachable E hBpos hB hab hcd hav hbv omega hxp hyp hxd hyd p q

/--
[PeriodicPlaneEmbedding.bufferedCrossings_openCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean)
-/
@[path]
private lemma bufferedCrossings_openCluster_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B a b c d : ℝ}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hBpos : 0 < B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B)
  (hH : omega ∈ E.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B))
  (hV : omega ∈ E.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d) :
-- imply
  ∃ xp yp : E.RectVertex a b (c + 4 * B) (d - 4 * B), ∃ xd yd : E.RectVertex (a + 4 * B) (b - 4 * B) c d, E.rectLeftBoundary a b (c + 4 * B) (d - 4 * B) xp ∧ E.rectRightBoundary a b (c + 4 * B) (d - 4 * B) yp ∧ E.rectBottomBoundary (a + 4 * B) (b - 4 * B) c d xd ∧ E.rectTopBoundary (a + 4 * B) (b - 4 * B) c d yd ∧ (P.openSubgraph omega).Reachable xp.1 yp.1 ∧ (P.openSubgraph omega).Reachable xd.1 yd.1 ∧ (P.openSubgraph omega).Reachable xp.1 xd.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.bufferedCrossings_openCluster E hBpos hB hab hcd omega hH hV

/--
[PeriodicPlaneEmbedding.overlapCrossings_glue_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean)
-/
@[path]
private lemma overlapCrossings_glue_horizontal_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B a l m b c d : ℝ}
-- given
  (hBpos : 0 < B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hal : a ≤ l)
  (hmb : m ≤ b)
  (hleft : a + 5 * B < m - 5 * B)
  (hright : l + 5 * B < b - 5 * B)
  (hheight : c + 5 * B < d - 5 * B) :
-- imply
  E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B) ∩ (E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B) ∩ E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d) ⊆ E.horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.overlapCrossings_glue_horizontal E hBpos hB hal hmb hleft hright hheight


-- created on 2026-10-23
