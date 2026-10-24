import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding
open StatMech StatMech.FrontierA StatMech.FrontierA.FiniteCellularGraphEmbedding


/--
[finiteGraphEdge.dart_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean)
-/
@[path]
private lemma dart_edge_eq
  [Fintype V]
  [DecidableEq V]
  {edge : finiteGraphEdge G} :
-- imply
  (edge.dart G).edge = edge.1 := by
-- proof
  apply StatMech.FrontierA.finiteGraphEdge.dart_edge edge

/--
[finiteGraphEdge.edgeFlip_isSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean)
-/
@[path]
private lemma edgeFlip_isSwap_eq
  [Fintype V]
  [DecidableEq V]
  {edge : finiteGraphEdge G} :
-- imply
  (edge.edgeFlip G).IsSwap := by
-- proof
  apply StatMech.FrontierA.finiteGraphEdge.edgeFlip_isSwap edge

/--
[finiteGraphEdge.dart_edge_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean)
-/
@[path]
private lemma dart_edge_ne_eq
  [Fintype V]
  [DecidableEq V]
  {edge edge' : finiteGraphEdge G}
-- given
  (hne : edge ≠ edge') :
-- imply
  (edge.dart G).edge ≠ (edge'.dart G).edge := by
-- proof
  apply StatMech.FrontierA.finiteGraphEdge.dart_edge_ne hne

/--
[finiteGraphEdge.edgeFlip_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean)
-/
@[path]
private lemma edgeFlip_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {edge edge' : finiteGraphEdge G}
-- given
  (hne : edge ≠ edge') :
-- imply
  (edge.edgeFlip G).Disjoint (edge'.edgeFlip G) := by
-- proof
  apply StatMech.FrontierA.finiteGraphEdge.edgeFlip_disjoint hne

/--
[finiteGraphEdge.edgeFlip_commute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean)
-/
@[path]
private lemma edgeFlip_commute_eq
  [Fintype V]
  [DecidableEq V]
  {edge edge' : finiteGraphEdge G}
-- given
  (hne : edge ≠ edge') :
-- imply
  Commute (edge.edgeFlip G) (edge'.edgeFlip G) := by
-- proof
  apply StatMech.FrontierA.finiteGraphEdge.edgeFlip_commute hne

/--
[ribbonSystem_boundaryParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean)
-/
@[path]
private lemma ribbonSystem_boundaryParity_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : FiniteCellularGraphEmbedding G} :
-- imply
  forall edges : Finset (finiteGraphEdge G), (edgesᶜ.card + embedding.ribbonSystem.boundaryComponents edges) % 2 = embedding.faceCount % 2 := by
-- proof
  apply StatMech.FrontierA.FiniteCellularGraphEmbedding.ribbonSystem_boundaryParity embedding

/--
[isoradialCritical_subgraphSum_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean)
-/
@[path]
private lemma isoradialCritical_subgraphSum_duality_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : FiniteCellularGraphEmbedding G}
-- given
  (character : forall F : Finset (finiteGraphEdge G), Fin (embedding.ribbonSystem.boundaryComponents F) -> Complex)
  (hcharacter : forall (F : Finset (finiteGraphEdge G)) (boundary : Fin (embedding.ribbonSystem.boundaryComponents F)), character F boundary ≠ 0)
  (htotal : forall F : Finset (finiteGraphEdge G), ∏ boundary, character F boundary = 1)
  (theta : finiteGraphEdge G -> Real)
  (htheta : forall edge, 0 < theta edge)
  (htheta' : forall edge, theta edge < Real.pi / 2) :
-- imply
  kwDualSubgraphSum (dualRibbonBoundaryCharacterCoefficient embedding.ribbonSystem character) (fun edge => isoradialCriticalMu (Real.pi / 2 - theta edge)) = (-1 : Complex) ^ embedding.faceCount * ((∏ edge : finiteGraphEdge G, isoradialCriticalMu (theta edge))⁻¹ * kwDualSubgraphSum (ribbonBoundaryCharacterCoefficient embedding.ribbonSystem character) (fun edge => isoradialCriticalMu (theta edge))) := by
-- proof
  apply StatMech.FrontierA.FiniteCellularGraphEmbedding.isoradialCritical_subgraphSum_duality embedding character hcharacter htotal theta htheta htheta'


-- created on 2026-10-23
