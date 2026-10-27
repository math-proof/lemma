import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneBarrier
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneBarrier StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[joined_boundary_arms_intersect_transverse_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneBarrier.lean)
-/
@[path]
private lemma joined_boundary_arms_intersect_transverse_path_eq
  {a b c d : ℝ}
  {lo hi j gl gr : Fin 2 → ℝ}
  {lower : Path lo j}
  {upper : Path hi j}
  {gamma : Path gl gr}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hgl : gl 0 < a)
  (hgr : b < gr 0)
  (hlo : lo 1 < c)
  (hhi : d < hi 1)
  (hlowerX : ∀ t : unitInterval, a < lower t 0 ∧ lower t 0 < b)
  (hupperX : ∀ t : unitInterval, a < upper t 0 ∧ upper t 0 < b)
  (hgammaY : ∀ t : unitInterval, c < gamma t 1 ∧ gamma t 1 < d) :
-- imply
  (Set.range gamma ∩ (Set.range lower ∪ Set.range upper)).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneBarrier.joined_boundary_arms_intersect_transverse_path hab hcd lower upper gamma hgl hgr hlo hhi hlowerX hupperX hgammaY

/--
[no_open_dual_transverse_walk_of_joined_primal_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneBarrier.lean)
-/
@[path]
private lemma no_open_dual_transverse_walk_of_joined_primal_arms_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {a b c d : ℝ}
  {xl xu xj : V}
  {yl yr : W}
  {lower : P.graph.Walk xl xj}
  {upper : P.graph.Walk xu xj}
  {dual : Pdual.graph.Walk yl yr}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hlowerNil : ¬ lower.Nil)
  (hupperNil : ¬ upper.Nil)
  (hdualNil : ¬ dual.Nil)
  (hlowerOpen : ∀ {x y : V}, s(x, y) ∈ lower.edges → omega s(x, y) = true)
  (hupperOpen : ∀ {x y : V}, s(x, y) ∈ upper.edges → omega s(x, y) = true)
  (hdualOpen : ∀ {x y : W}, s(x, y) ∈ dual.edges → dualConfigEquiv D.edgeDual omega s(x, y) = true)
  (hdualLeft : D.primalEmbedding.coordinates (D.dualEmbedding.vertex yl) 0 < a)
  (hdualRight : b < D.primalEmbedding.coordinates (D.dualEmbedding.vertex yr) 0)
  (hlowerBottom : D.primalEmbedding.vertexCoord xl 1 < c)
  (hupperTop : d < D.primalEmbedding.vertexCoord xu 1)
  (hlowerX : ∀ t : unitInterval, a < D.primalEmbedding.coordinates (D.primalEmbedding.walkArc lower t) 0 ∧ D.primalEmbedding.coordinates (D.primalEmbedding.walkArc lower t) 0 < b)
  (hupperX : ∀ t : unitInterval, a < D.primalEmbedding.coordinates (D.primalEmbedding.walkArc upper t) 0 ∧ D.primalEmbedding.coordinates (D.primalEmbedding.walkArc upper t) 0 < b)
  (hdualY : ∀ t : unitInterval, c < D.primalEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 ∧ D.primalEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 < d) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_open_dual_transverse_walk_of_joined_primal_arms D omega hab hcd lower upper dual hlowerNil hupperNil hdualNil hlowerOpen hupperOpen hdualOpen hdualLeft hdualRight hlowerBottom hupperTop hlowerX hupperX hdualY


-- created on 2026-10-23
