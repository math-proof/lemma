import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldTransverseAssembly
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicPlaneEmbedding.walkArc_coord_strict_bounds_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTransverseAssembly.lean)
-/
@[path]
private lemma walkArc_coord_strict_bounds_of_support_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B c d : Real}
  {i : Fin 2}
  {x y : V}
  {p : P.graph.Walk x y}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2), |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
  (hp : ∀ v ∈ p.support, c + B < E.vertexCoord v i ∧ E.vertexCoord v i < d - B) :
-- imply
  ∀ t : unitInterval, c < E.coordinates (E.walkArc p t) i ∧ E.coordinates (E.walkArc p t) i < d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.walkArc_coord_strict_bounds_of_support E hB0 hB i p hp

/--
[finiteStripPrimal_dualPairConnection_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTransverseAssembly.lean)
-/
@[path]
private lemma finiteStripPrimal_dualPairConnection_disjoint_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {Bp Bd r s : Real}
  {gap : Int}
  {np N : Nat}
  {Lp Rp : Finset V}
  {Ld Rd : Finset W}
-- given
  (hBp0 : 0 ≤ Bp)
  (hBd0 : 0 ≤ Bd)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
  (hgap : 0 < (gap : Real))
  (hLpDeep : (Lp : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
  (hLd : ∀ y ∈ Ld, D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 < r - Bp - 1)
  (hRd : ∀ y ∈ Rd, r + np + Bp + 1 < D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0)
  (hbox : ∀ v ∈ Pdual.orbitBox (Pdual.bufferedRadius N), (2 * s + (s + gap)) / 3 + Bd < D.dualEmbedding.vertexCoord v 1 ∧ D.dualEmbedding.vertexCoord v 1 < (s + 2 * (s + gap)) / 3 - Bd)
  (hprimal : omega ∈ D.primalEmbedding.finiteStripJoinedBoundaryArmEvent r s (s + gap) np Lp Rp)
  (hdual : dualConfigEquiv D.edgeDual omega ∈ Pdual.finiteInfinitePairConnectionEvent Ld Rd N) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.finiteStripPrimal_dualPairConnection_disjoint D omega hBp0 hBd0 hBp hBd hgap hLpDeep hLd hRd hbox hprimal hdual


-- created on 2026-10-23
