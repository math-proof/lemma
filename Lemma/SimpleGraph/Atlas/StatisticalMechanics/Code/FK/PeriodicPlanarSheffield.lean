import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicPlaneEmbedding.vertexCoord_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma vertexCoord_shift_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {x : V}
  {i : Fin 2} :
-- imply
  E.vertexCoord (P.shift z x) i = E.vertexCoord x i + z i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.vertexCoord_shift E z x i

/--
[PeriodicPlaneEmbedding.fundamentalArcDisplacements_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma fundamentalArcDisplacements_isCompact_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P} :
-- imply
  IsCompact E.fundamentalArcDisplacements := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.fundamentalArcDisplacements_isCompact E

/--
[PeriodicPlaneEmbedding.exists_edgeArc_displacement_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma exists_edgeArc_displacement_bound_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P} :
-- imply
  ∃ B : ℝ, 0 ≤ B ∧ ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_edgeArc_displacement_bound E

/--
[PeriodicPlaneEmbedding.edgeArc_mem_expanded_planeRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma edgeArc_mem_expanded_planeRect_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {a b c d : ℝ}
  {x y : V}
  (t)
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hxy : P.graph.Adj x y)
  (hx : E.vertex x ∈ E.planeRect a b c d) :
-- imply
  E.edgeArc hxy t ∈ E.planeRect (a - B) (b + B) (c - B) (d + B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.edgeArc_mem_expanded_planeRect E hB hxy hx

/--
[PeriodicPlaneEmbedding.edgeArc_coord_le_vertex_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma edgeArc_coord_le_vertex_add_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {x y : V}
  (t)
  {i : Fin 2}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hxy : P.graph.Adj x y) :
-- imply
  E.coordinates (E.edgeArc hxy t) i ≤ E.vertexCoord x i + B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.edgeArc_coord_le_vertex_add E hB hxy i

/--
[PeriodicPlaneEmbedding.vertex_sub_le_edgeArc_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma vertex_sub_le_edgeArc_coord_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {x y : V}
  (t)
  {i : Fin 2}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hxy : P.graph.Adj x y) :
-- imply
  E.vertexCoord x i - B ≤ E.coordinates (E.edgeArc hxy t) i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.vertex_sub_le_edgeArc_coord E hB hxy i

/--
[PeriodicPlaneEmbedding.walkArc_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma walkArc_nil_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {x : V} :
-- imply
  E.walkArc (.nil : P.graph.Walk x x) = Path.refl _ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.walkArc_nil E x

/--
[PeriodicPlaneEmbedding.walkArc_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma walkArc_cons_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {x y z : V}
  {p : P.graph.Walk y z}
-- given
  (hxy : P.graph.Adj x y) :
-- imply
  E.walkArc (p.cons hxy) = (E.edgeArc hxy).trans (E.walkArc p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.walkArc_cons E hxy p

/--
[PeriodicPlaneEmbedding.mem_walkArc_range_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma mem_walkArc_range_cases_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {x y : V}
  {p : P.graph.Walk x y}
  {q : ℂ}
-- given
  (hq : q ∈ Set.range (E.walkArc p)) :
-- imply
  q = E.vertex x ∨ ∃ u v : V, ∃ huv : P.graph.Adj u v, s(u, v) ∈ p.edges ∧ q ∈ Set.range (E.edgeArc huv) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.mem_walkArc_range_cases E p hq

/--
[PeriodicPlaneEmbedding.mem_walkArc_range_of_not_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma mem_walkArc_range_of_not_nil_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {x y : V}
  {p : P.graph.Walk x y}
  {q : ℂ}
-- given
  (hp : ¬ p.Nil)
  (hq : q ∈ Set.range (E.walkArc p)) :
-- imply
  ∃ u v : V, ∃ huv : P.graph.Adj u v, s(u, v) ∈ p.edges ∧ q ∈ Set.range (E.edgeArc huv) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.mem_walkArc_range_of_not_nil E p hp hq

/--
[PeriodicPlaneEmbedding.walkArc_range_subset_expanded_planeRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma walkArc_range_subset_expanded_planeRect_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {a b c d : ℝ}
  {x y : V}
  {p : P.graph.Walk x y}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hp : ∀ v, v ∈ p.support → E.vertex v ∈ E.planeRect a b c d) :
-- imply
  Set.range (E.walkArc p) ⊆ E.planeRect (a - B) (b + B) (c - B) (d + B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.walkArc_range_subset_expanded_planeRect E hB0 hB p hp

/--
[PeriodicPlaneEmbedding.rectVertices_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma rectVertices_finite_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ} :
-- imply
  (E.rectVertices a b c d).Finite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectVertices_finite E a b c d

/--
[PeriodicPlaneEmbedding.openRectWalkArc_range_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma openRectWalkArc_range_subset_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {a b c d : ℝ}
  {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
  {x y : E.RectVertex a b c d}
  {p : (FK.openSub (E.rectGraph a b c d) eta).Walk x y}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B) :
-- imply
  Set.range (E.walkArc (p.map (E.openRectHom a b c d eta))) ⊆ E.planeRect (a - B) (b + B) (c - B) (d + B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.openRectWalkArc_range_subset E hB0 hB p

/--
[PeriodicPlaneEmbedding.continuous_rectRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma continuous_rectRestrict_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ} :
-- imply
  Continuous (E.rectRestrict a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.continuous_rectRestrict E a b c d

/--
[PeriodicPlaneEmbedding.openRectWalk_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma openRectWalk_edge_open_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ}
  {omega : ConfigSpace (Sym2 V)}
  {x y : E.RectVertex a b c d}
  {p : (FK.openSub (E.rectGraph a b c d) (E.rectRestrict a b c d omega)).Walk x y}
  {u v : V}
-- given
  (huv : s(u, v) ∈ (p.map (E.openRectHom a b c d (E.rectRestrict a b c d omega))).edges) :
-- imply
  omega s(u, v) = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.openRectWalk_edge_open E p huv

/--
[PeriodicPlaneEmbedding.mem_openRectWalkArc_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma mem_openRectWalkArc_range_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ}
  {omega : ConfigSpace (Sym2 V)}
  {x y : E.RectVertex a b c d}
  {p : (FK.openSub (E.rectGraph a b c d) (E.rectRestrict a b c d omega)).Walk x y}
  {q : ℂ}
-- given
  (hp : ¬ (p.map (E.openRectHom a b c d (E.rectRestrict a b c d omega))).Nil)
  (hq : q ∈ Set.range (E.walkArc (p.map (E.openRectHom a b c d (E.rectRestrict a b c d omega))))) :
-- imply
  ∃ u v : V, ∃ huv : P.graph.Adj u v, omega s(u, v) = true ∧ q ∈ Set.range (E.edgeArc huv) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.mem_openRectWalkArc_range E p hp hq

/--
[PeriodicPlaneEmbedding.rectLeftBoundary_coord_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma rectLeftBoundary_coord_lt_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B a b c d : ℝ}
  {x : E.RectVertex a b c d}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hx : E.rectLeftBoundary a b c d x) :
-- imply
  E.vertexCoord x.1 0 < a + B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectLeftBoundary_coord_lt E hB hx

/--
[PeriodicPlaneEmbedding.rectRightBoundary_coord_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma rectRightBoundary_coord_gt_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B a b c d : ℝ}
  {x : E.RectVertex a b c d}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hx : E.rectRightBoundary a b c d x) :
-- imply
  b - B < E.vertexCoord x.1 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRightBoundary_coord_gt E hB hx

/--
[PeriodicPlaneEmbedding.rectBottomBoundary_coord_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma rectBottomBoundary_coord_lt_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B a b c d : ℝ}
  {x : E.RectVertex a b c d}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hx : E.rectBottomBoundary a b c d x) :
-- imply
  E.vertexCoord x.1 1 < c + B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectBottomBoundary_coord_lt E hB hx

/--
[PeriodicPlaneEmbedding.rectTopBoundary_coord_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma rectTopBoundary_coord_gt_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B a b c d : ℝ}
  {x : E.RectVertex a b c d}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hx : E.rectTopBoundary a b c d x) :
-- imply
  d - B < E.vertexCoord x.1 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTopBoundary_coord_gt E hB hx

/--
[PeriodicPlaneEmbedding.finiteHorizontalCrossing_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma finiteHorizontalCrossing_isIncreasing_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ} :
-- imply
  IsIncreasing (E.finiteHorizontalCrossing a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteHorizontalCrossing_isIncreasing E a b c d

/--
[PeriodicPlaneEmbedding.rectRestrict_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma rectRestrict_mono_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ} :
-- imply
  Monotone (E.rectRestrict a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRestrict_mono E a b c d

/--
[PeriodicPlaneEmbedding.horizontalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma horizontalCrossingEvent_isIncreasing_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ} :
-- imply
  IsIncreasing (E.horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossingEvent_isIncreasing E a b c d

/--
[PeriodicPlaneEmbedding.horizontalCrossingEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma horizontalCrossingEvent_measurableSet_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ} :
-- imply
  MeasurableSet (E.horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossingEvent_measurableSet E a b c d

/--
[PeriodicPlaneEmbedding.finiteHorizontalCrossing_embeddedPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma finiteHorizontalCrossing_embeddedPath_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {a b c d : ℝ}
  {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (heta : eta ∈ E.finiteHorizontalCrossing a b c d) :
-- imply
  ∃ x y : E.RectVertex a b c d, E.rectLeftBoundary a b c d x ∧ E.rectRightBoundary a b c d y ∧ ∃ gamma : Path (E.vertex x.1) (E.vertex y.1), Set.range gamma ⊆ E.planeRect (a - B) (b + B) (c - B) (d + B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteHorizontalCrossing_embeddedPath E hB0 hB heta

/--
[PeriodicPlaneEmbedding.finiteHorizontalCrossing_openWalk_of_wide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma finiteHorizontalCrossing_openWalk_of_wide_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {a b c d : ℝ}
  {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hwide : a + B ≤ b - B)
  (heta : eta ∈ E.finiteHorizontalCrossing a b c d) :
-- imply
  ∃ x y : E.RectVertex a b c d, E.rectLeftBoundary a b c d x ∧ E.rectRightBoundary a b c d y ∧ ∃ p : (FK.openSub (E.rectGraph a b c d) eta).Walk x y, ¬ (p.map (E.openRectHom a b c d eta)).Nil := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteHorizontalCrossing_openWalk_of_wide E hB hwide heta

/--
[PeriodicPlaneEmbedding.finiteHorizontalCrossing_extendedPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma finiteHorizontalCrossing_extendedPath_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {a b c d : ℝ}
  {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (heta : eta ∈ E.finiteHorizontalCrossing a b c d) :
-- imply
  ∃ xl xr : V, ∃ gamma : Path (E.vertex xl) (E.vertex xr), E.vertexCoord xl 0 < a ∧ b < E.vertexCoord xr 0 ∧ Set.range gamma ⊆ E.planeRect (a - B) (b + B) (c - B) (d + B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteHorizontalCrossing_extendedPath E hB0 hB heta

/--
[PeriodicPlaneEmbedding.finiteVerticalCrossing_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma finiteVerticalCrossing_isIncreasing_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ} :
-- imply
  IsIncreasing (E.finiteVerticalCrossing a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteVerticalCrossing_isIncreasing E a b c d

/--
[PeriodicPlaneEmbedding.verticalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma verticalCrossingEvent_isIncreasing_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ} :
-- imply
  IsIncreasing (E.verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossingEvent_isIncreasing E a b c d

/--
[PeriodicPlaneEmbedding.verticalCrossingEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma verticalCrossingEvent_measurableSet_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : ℝ} :
-- imply
  MeasurableSet (E.verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossingEvent_measurableSet E a b c d

/--
[PeriodicPlaneEmbedding.finiteVerticalCrossing_embeddedPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma finiteVerticalCrossing_embeddedPath_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {a b c d : ℝ}
  {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (heta : eta ∈ E.finiteVerticalCrossing a b c d) :
-- imply
  ∃ x y : E.RectVertex a b c d, E.rectBottomBoundary a b c d x ∧ E.rectTopBoundary a b c d y ∧ ∃ gamma : Path (E.vertex x.1) (E.vertex y.1), Set.range gamma ⊆ E.planeRect (a - B) (b + B) (c - B) (d + B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteVerticalCrossing_embeddedPath E hB0 hB heta

/--
[PeriodicPlaneEmbedding.finiteVerticalCrossing_openWalk_of_tall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma finiteVerticalCrossing_openWalk_of_tall_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {a b c d : ℝ}
  {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (htall : c + B ≤ d - B)
  (heta : eta ∈ E.finiteVerticalCrossing a b c d) :
-- imply
  ∃ x y : E.RectVertex a b c d, E.rectBottomBoundary a b c d x ∧ E.rectTopBoundary a b c d y ∧ ∃ p : (FK.openSub (E.rectGraph a b c d) eta).Walk x y, ¬ (p.map (E.openRectHom a b c d eta)).Nil := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteVerticalCrossing_openWalk_of_tall E hB htall heta

/--
[PeriodicPlaneEmbedding.finiteVerticalCrossing_extendedPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma finiteVerticalCrossing_extendedPath_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B : ℝ}
  {a b c d : ℝ}
  {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (heta : eta ∈ E.finiteVerticalCrossing a b c d) :
-- imply
  ∃ xb xt : V, ∃ gamma : Path (E.vertex xb) (E.vertex xt), E.vertexCoord xb 1 < c ∧ d < E.vertexCoord xt 1 ∧ Set.range gamma ⊆ E.planeRect (a - B) (b + B) (c - B) (d + B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteVerticalCrossing_extendedPath E hB0 hB heta

/--
[PeriodicGraph.shift_neg_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma shift_neg_shift_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {x : V} :
-- imply
  P.shift (-z) (P.shift z x) = x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shift_neg_shift P z x

/--
[PeriodicGraph.shift_shift_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma shift_shift_neg_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {x : V} :
-- imply
  P.shift z (P.shift (-z) x) = x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shift_shift_neg P z x

/--
[PeriodicGraph.configTranslate_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma configTranslate_neg_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.configTranslate (-z) (P.configTranslate z omega) = omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.configTranslate_neg P z omega

/--
[PeriodicGraph.measurable_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma measurable_configTranslate_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2} :
-- imply
  Measurable (P.configTranslate z) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurable_configTranslate P z

/--
[PeriodicGraph.configTranslate_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma configTranslate_mono_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2} :
-- imply
  Monotone (P.configTranslate z) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.configTranslate_mono P z

/--
[PeriodicGraph.translateEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma translateEvent_measurableSet_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hA : MeasurableSet A) :
-- imply
  MeasurableSet (P.translateEvent z A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.translateEvent_measurableSet P z hA

/--
[PeriodicGraph.translateEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma translateEvent_isIncreasing_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (P.translateEvent z A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.translateEvent_isIncreasing P z hA

/--
[PeriodicGraph.translateEvent_measure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma translateEvent_measure_eq_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hA : MeasurableSet A) :
-- imply
  mu (P.translateEvent z A) = mu A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.translateEvent_measure_eq P mu hTI z hA

/--
[PeriodicGraph.openSubgraphTranslateHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma openSubgraphTranslateHom_apply_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {x : V} :
-- imply
  P.openSubgraphTranslateHom z omega x = P.shift z x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.openSubgraphTranslateHom_apply P z omega x

/--
[PeriodicGraph.reachable_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma reachable_configTranslate_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V} :
-- imply
  (P.openSubgraph (P.configTranslate z omega)).Reachable (P.shift z x) (P.shift z y) ↔ (P.openSubgraph omega).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.reachable_configTranslate P z omega x y

/--
[PeriodicGraph.cluster_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma cluster_configTranslate_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {x : V} :
-- imply
  P.cluster (P.configTranslate z omega) (P.shift z x) = P.shift z '' P.cluster omega x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.cluster_configTranslate P z omega x

/--
[PeriodicGraph.cluster_infinite_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma cluster_infinite_configTranslate_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {x : V} :
-- imply
  (P.cluster (P.configTranslate z omega) (P.shift z x)).Infinite ↔ (P.cluster omega x).Infinite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.cluster_infinite_configTranslate P z omega x

/--
[measurable_sqrt_trick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma measurable_sqrt_trick_eq
  [DecidableEq V]
  [DecidableEq W]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (hFKG : IsFKG mu)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B) :
-- imply
  1 - Real.sqrt (1 - mu.real (A ∪ B)) <= max (mu.real A) (mu.real B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.measurable_sqrt_trick mu hFKG hA hB hAm hBm

/--
[four_event_sqrt_trick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma four_event_sqrt_trick_eq
  [DecidableEq V]
  [DecidableEq W]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {A B C D : Set (ConfigSpace (Sym2 V))}
-- given
  (hFKG : IsFKG mu)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hC : IsIncreasing C)
  (hD : IsIncreasing D)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B)
  (hCm : MeasurableSet C)
  (hDm : MeasurableSet D) :
-- imply
  1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤ max (max (mu.real A) (mu.real B)) (max (mu.real C) (mu.real D)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.four_event_sqrt_trick mu hFKG hA hB hC hD hAm hBm hCm hDm

/--
[four_event_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma four_event_max_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {A B C D : ℕ → Set (ConfigSpace (Sym2 V))}
-- given
  (hFKG : IsFKG mu)
  (hA : ∀ n, IsIncreasing (A n))
  (hB : ∀ n, IsIncreasing (B n))
  (hC : ∀ n, IsIncreasing (C n))
  (hD : ∀ n, IsIncreasing (D n))
  (hAm : ∀ n, MeasurableSet (A n))
  (hBm : ∀ n, MeasurableSet (B n))
  (hCm : ∀ n, MeasurableSet (C n))
  (hDm : ∀ n, MeasurableSet (D n))
  (hunion : Tendsto (fun n => mu.real (A n ∪ (B n ∪ (C n ∪ D n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (max (mu.real (A n)) (mu.real (B n))) (max (mu.real (C n)) (mu.real (D n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.four_event_max_tendsto_one mu hFKG A B C D hA hB hC hD hAm hBm hCm hDm hunion

/--
[min_tendsto_zero_of_matched_exclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma min_tendsto_zero_of_matched_exclusion_eq
  [DecidableEq V]
  [DecidableEq W]
  {primalH primalV dualV dualH : ℕ → ℝ}
-- given
  (hH0 : ∀ n, 0 ≤ primalH n)
  (hV0 : ∀ n, 0 ≤ primalV n)
  (hmatchH : ∀ n, primalH n + dualV n ≤ 1)
  (hmatchV : ∀ n, primalV n + dualH n ≤ 1)
  (hdual : Tendsto (fun n => max (dualV n) (dualH n)) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => min (primalH n) (primalV n)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.min_tendsto_zero_of_matched_exclusion primalH primalV dualV dualH hH0 hV0 hmatchH hmatchV hdual

/--
[balanced_aspect_crossing_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma balanced_aspect_crossing_contradiction_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (h v hNext vNext : ℕ → ℝ)
  (hbalance : ∀ n, h n ≤ v n)
  (hnext : ∀ n, vNext n < hNext n)
  (hmax : Tendsto (fun n => max (h n) (vNext n)) atTop (nhds 1))
  (hmin : Tendsto (fun n => min (v n) (h n)) atTop (nhds 0))
  (hminNext : Tendsto (fun n => min (vNext n) (hNext n)) atTop (nhds 0)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.balanced_aspect_crossing_contradiction h v hNext vNext hbalance hnext hmax hmin hminNext

/--
[balanced_aspect_crossing_contradiction_of_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma balanced_aspect_crossing_contradiction_of_error_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (h v hNext vNext error : ℕ → ℝ)
  (hh0 : ∀ n, 0 ≤ h n)
  (hvNext0 : ∀ n, 0 ≤ vNext n)
  (herror0 : ∀ n, 0 ≤ error n)
  (hbalance : ∀ n, h n ≤ v n + error n)
  (hnext : ∀ n, vNext n ≤ hNext n + error n)
  (herror : Tendsto error atTop (nhds 0))
  (hmax : Tendsto (fun n => max (h n) (vNext n)) atTop (nhds 1))
  (hmin : Tendsto (fun n => min (v n) (h n)) atTop (nhds 0))
  (hminNext : Tendsto (fun n => min (vNext n) (hNext n)) atTop (nhds 0)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.balanced_aspect_crossing_contradiction_of_error h v hNext vNext error hh0 hvNext0 herror0 hbalance hnext herror hmax hmin hminNext

/--
[measurable_forceOpenFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma measurable_forceOpenFinset_eq
  [DecidableEq V]
  [DecidableEq W]
  {F : Finset (Sym2 V)} :
-- imply
  Measurable (forceOpenFinset F : ConfigSpace (Sym2 V) → ConfigSpace (Sym2 V)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.measurable_forceOpenFinset F

/--
[PeriodicGraph.measurableSet_openChain_sheffield](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma measurableSet_openChain_sheffield_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {l : List V} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | List.IsChain (P.openSubgraph omega).Adj l} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_openChain_sheffield P l

/--
[PeriodicGraph.reachable_iff_openChain_sheffield](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma reachable_iff_openChain_sheffield_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V} :
-- imply
  (P.openSubgraph omega).Reachable x y ↔ ∃ l : List V, List.IsChain (P.openSubgraph omega).Adj (x :: l) ∧ (x :: l).getLast (List.cons_ne_nil _ _) = y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.reachable_iff_openChain_sheffield P omega x y

/--
[PeriodicGraph.connectedWithinOrbit_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma connectedWithinOrbit_measurableSet_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {x y : V}
  {N : ℕ} :
-- imply
  MeasurableSet (P.connectedWithinOrbit x y N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.connectedWithinOrbit_measurableSet P x y N

/--
[PeriodicGraph.connectedWithinOrbit_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma connectedWithinOrbit_isIncreasing_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {x y : V}
  {N : ℕ} :
-- imply
  IsIncreasing (P.connectedWithinOrbit x y N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.connectedWithinOrbit_isIncreasing P x y N

/--
[PeriodicGraph.connectedWithinOrbit_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma connectedWithinOrbit_mono_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {x y : V} :
-- imply
  Monotone (P.connectedWithinOrbit x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.connectedWithinOrbit_mono P x y

/--
[PeriodicGraph.iUnion_connectedWithinOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma iUnion_connectedWithinOrbit_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {x y : V} :
-- imply
  (⋃ N, P.connectedWithinOrbit x y N) = P.twoPointEvent x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iUnion_connectedWithinOrbit P x y

/--
[PeriodicGraph.hasUniqueInfiniteCluster_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma hasUniqueInfiniteCluster_configTranslate_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.HasUniqueInfiniteCluster (P.configTranslate z omega) ↔ P.HasUniqueInfiniteCluster omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.hasUniqueInfiniteCluster_configTranslate P z omega

/--
[PeriodicGraph.clusterInfinite_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma clusterInfinite_isIncreasing_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {x : V} :
-- imply
  IsIncreasing {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterInfinite_isIncreasing P x

/--
[PeriodicGraph.orbitBoxHitsInfinite_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma orbitBoxHitsInfinite_measurableSet_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  MeasurableSet (P.orbitBoxHitsInfinite n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitBoxHitsInfinite_measurableSet P n

/--
[PeriodicGraph.orbitBoxHitsInfinite_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma orbitBoxHitsInfinite_isIncreasing_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  IsIncreasing (P.orbitBoxHitsInfinite n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitBoxHitsInfinite_isIncreasing P n

/--
[PeriodicGraph.translatedOrbitBoxHitsInfinite_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma translatedOrbitBoxHitsInfinite_preimage_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n : ℕ} :
-- imply
  P.configTranslate z ⁻¹' P.translatedOrbitBoxHitsInfinite z n = P.orbitBoxHitsInfinite n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.translatedOrbitBoxHitsInfinite_preimage P z n

/--
[PeriodicGraph.translatedOrbitBoxHitsInfinite_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma translatedOrbitBoxHitsInfinite_measurableSet_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n : ℕ} :
-- imply
  MeasurableSet (P.translatedOrbitBoxHitsInfinite z n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.translatedOrbitBoxHitsInfinite_measurableSet P z n

/--
[PeriodicGraph.translatedOrbitBoxHitsInfinite_measure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma translatedOrbitBoxHitsInfinite_measure_eq_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {n : ℕ}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu (P.translatedOrbitBoxHitsInfinite z n) = mu (P.orbitBoxHitsInfinite n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.translatedOrbitBoxHitsInfinite_measure_eq P mu hTI z n

/--
[PeriodicGraph.orbitBoxHitsInfinite_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma orbitBoxHitsInfinite_mono_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V} :
-- imply
  Monotone P.orbitBoxHitsInfinite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitBoxHitsInfinite_mono P

/--
[PeriodicGraph.iUnion_orbitBoxHitsInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma iUnion_orbitBoxHitsInfinite_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V} :
-- imply
  (⋃ n, P.orbitBoxHitsInfinite n) = {omega | P.HasInfiniteCluster omega} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iUnion_orbitBoxHitsInfinite P

/--
[PeriodicGraph.orbitBoxHitsInfinite_real_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma orbitBoxHitsInfinite_real_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hexists : mu {omega | P.HasInfiniteCluster omega} = 1) :
-- imply
  Tendsto (fun n => mu.real (P.orbitBoxHitsInfinite n)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitBoxHitsInfinite_real_tendsto_one P mu hexists

/--
[PeriodicGraph.measurableSet_hasUniqueInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma measurableSet_hasUniqueInfiniteCluster_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_hasUniqueInfiniteCluster P

/--
[PeriodicGraph.pairMergeError_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma pairMergeError_measurableSet_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {x y : V}
  {N : ℕ} :
-- imply
  MeasurableSet (P.pairMergeError x y N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.pairMergeError_measurableSet P x y N

/--
[PeriodicGraph.pairMergeError_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma pairMergeError_antitone_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {x y : V} :
-- imply
  Antitone (P.pairMergeError x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.pairMergeError_antitone P x y

/--
[PeriodicGraph.iInter_pairMergeError_subset_not_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma iInter_pairMergeError_subset_not_unique_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {x y : V} :
-- imply
  (⋂ N, P.pairMergeError x y N) ⊆ {omega | P.HasUniqueInfiniteCluster omega}ᶜ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iInter_pairMergeError_subset_not_unique P x y

/--
[PeriodicGraph.pairMergeError_real_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma pairMergeError_real_tendsto_zero_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {x y : V}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  Tendsto (fun N => mu.real (P.pairMergeError x y N)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.pairMergeError_real_tendsto_zero P mu hunique x y

/--
[PeriodicGraph.pairMergeErrorUnion_real_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma pairMergeErrorUnion_real_tendsto_zero_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {L R : Finset V}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  Tendsto (fun N => mu.real (P.pairMergeErrorUnion L R N)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.pairMergeErrorUnion_real_tendsto_zero P mu hunique L R

/--
[PeriodicGraph.hasUniqueInfiniteCluster_translate_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma hasUniqueInfiniteCluster_translate_preimage_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2} :
-- imply
  P.configTranslate z ⁻¹' {omega | P.HasUniqueInfiniteCluster omega} = {omega | P.HasUniqueInfiniteCluster omega} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.hasUniqueInfiniteCluster_translate_preimage P z

/--
[PeriodicGraph.clusterInfinite_translate_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma clusterInfinite_translate_preimage_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {z : Site 2}
  {x : V} :
-- imply
  P.configTranslate z ⁻¹' {omega | (P.cluster omega (P.shift z x)).Infinite} = {omega | (P.cluster omega x).Infinite} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterInfinite_translate_preimage P z x

/--
[PeriodicGraph.exists_fundamental_clusterInfinite_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma exists_fundamental_clusterInfinite_pos_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hexists : mu {omega | P.HasInfiniteCluster omega} = 1) :
-- imply
  ∃ u ∈ P.fundamentalDomain, 0 < mu {omega | (P.cluster omega u).Infinite} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_fundamental_clusterInfinite_pos P mu hTI hexists

/--
[dual_planeRect_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma dual_planeRect_eq_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {a b c d : ℝ} :
-- imply
  D.dualEmbedding.planeRect a b c d = D.primalEmbedding.planeRect a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dual_planeRect_eq D a b c d

/--
[exists_common_edgeArc_displacement_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma exists_common_edgeArc_displacement_bound_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual} :
-- imply
  ∃ B : ℝ, 0 < B ∧ (∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B) ∧ (∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_common_edgeArc_displacement_bound D

/--
[dualConfigEquiv_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma dualConfigEquiv_configTranslate_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  dualConfigEquiv D.edgeDual (P.configTranslate z omega) = Pdual.configTranslate z (dualConfigEquiv D.edgeDual omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualConfigEquiv_configTranslate D z omega

/--
[dualMeasure_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma dualMeasure_isTranslationInvariant_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  Pdual.IsTranslationInvariant (D.dualMeasure mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_isTranslationInvariant D mu hTI

/--
[no_open_primal_dual_edge_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma no_open_primal_dual_edge_crossing_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
  {a b : W}
  {t u}
-- given
  (hxy : P.graph.Adj x y)
  (hab : Pdual.graph.Adj a b)
  (hopen : omega s(x, y) = true)
  (hdualOpen : dualConfigEquiv D.edgeDual omega s(a, b) = true)
  (hcross : D.primalEmbedding.edgeArc hxy t = D.dualEmbedding.edgeArc hab u) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_open_primal_dual_edge_crossing D omega hxy hab hopen hdualOpen hcross

/--
[no_open_primal_dual_walkArc_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma no_open_primal_dual_walkArc_crossing_eq
  [DecidableEq V]
  [DecidableEq W]
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
  Disjoint (Set.range (D.primalEmbedding.walkArc p)) (Set.range (D.dualEmbedding.walkArc q)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_open_primal_dual_walkArc_crossing D omega p q hp hq hpopen hqopen

/--
[no_openRectWalkArc_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma no_openRectWalkArc_crossing_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {ap bp cp dp ad bd cd dd : ℝ}
  {xp yp : D.primalEmbedding.RectVertex ap bp cp dp}
  {xd yd : D.dualEmbedding.RectVertex ad bd cd dd}
  {p : (FK.openSub (D.primalEmbedding.rectGraph ap bp cp dp) (D.primalEmbedding.rectRestrict ap bp cp dp omega)).Walk xp yp}
  {q : (FK.openSub (D.dualEmbedding.rectGraph ad bd cd dd) (D.dualEmbedding.rectRestrict ad bd cd dd (dualConfigEquiv D.edgeDual omega))).Walk xd yd}
-- given
  (hp : ¬ (p.map (D.primalEmbedding.openRectHom ap bp cp dp (D.primalEmbedding.rectRestrict ap bp cp dp omega))).Nil)
  (hq : ¬ (q.map (D.dualEmbedding.openRectHom ad bd cd dd (D.dualEmbedding.rectRestrict ad bd cd dd (dualConfigEquiv D.edgeDual omega)))).Nil) :
-- imply
  Disjoint (Set.range (D.primalEmbedding.walkArc (p.map (D.primalEmbedding.openRectHom ap bp cp dp (D.primalEmbedding.rectRestrict ap bp cp dp omega))))) (Set.range (D.dualEmbedding.walkArc (q.map (D.dualEmbedding.openRectHom ad bd cd dd (D.dualEmbedding.rectRestrict ad bd cd dd (dualConfigEquiv D.edgeDual omega)))))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_openRectWalkArc_crossing D omega p q hp hq

/--
[matchedCrossingEvents_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma matchedCrossingEvents_disjoint_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {B a b c d : ℝ}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B) :
-- imply
  Disjoint (D.primalEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B)) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedCrossingEvents_disjoint D hBpos hBp hBd hab hcd

/--
[matchedCrossing_measureReal_add_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma matchedCrossing_measureReal_add_le_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B a b c d : ℝ}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B) :
-- imply
  mu.real (D.primalEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B)) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d) ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one D mu hBpos hBp hBd hab hcd

/--
[exists_buffer_matchedCrossing_measureReal_add_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma exists_buffer_matchedCrossing_measureReal_add_le_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu] :
-- imply
  ∃ B : ℝ, 0 < B ∧ ∀ {a b c d : ℝ}, a + 5 * B < b - 5 * B → c + 5 * B < d - 5 * B → mu.real (D.primalEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B)) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d) ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_buffer_matchedCrossing_measureReal_add_le_one D mu

/--
[commonUniqueInfiniteClusterEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma commonUniqueInfiniteClusterEvent_measurableSet_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual} :
-- imply
  MeasurableSet D.commonUniqueInfiniteClusterEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.commonUniqueInfiniteClusterEvent_measurableSet D

/--
[commonUniqueInfiniteClusterEvent_translate_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma commonUniqueInfiniteClusterEvent_translate_preimage_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {z : Site 2} :
-- imply
  P.configTranslate z ⁻¹' D.commonUniqueInfiniteClusterEvent = D.commonUniqueInfiniteClusterEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.commonUniqueInfiniteClusterEvent_translate_preimage D z

/--
[commonUniqueInfiniteClusterEvent_measure_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma commonUniqueInfiniteClusterEvent_measure_eq_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hprimal : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hdual : mu ((dualConfigEquiv D.edgeDual) ⁻¹' {eta | Pdual.HasUniqueInfiniteCluster eta}) = 1) :
-- imply
  mu D.commonUniqueInfiniteClusterEvent = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.commonUniqueInfiniteClusterEvent_measure_eq_one D mu hprimal hdual

/--
[exists_primal_dual_fundamental_clusterInfinite_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean)
-/
@[path]
private lemma exists_primal_dual_fundamental_clusterInfinite_pos_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hprimal : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hdual : mu ((dualConfigEquiv D.edgeDual) ⁻¹' {eta | Pdual.HasUniqueInfiniteCluster eta}) = 1) :
-- imply
  (∃ u ∈ P.fundamentalDomain, 0 < mu {omega | (P.cluster omega u).Infinite}) ∧ (∃ w ∈ Pdual.fundamentalDomain, 0 < D.dualMeasure mu {eta | (Pdual.cluster eta w).Infinite}) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_primal_dual_fundamental_clusterInfinite_pos D mu hTI hprimal hdual


-- created on 2026-10-23
