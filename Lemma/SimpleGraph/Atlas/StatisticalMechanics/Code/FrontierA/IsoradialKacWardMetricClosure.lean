import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure.Part3
open Finset SimpleGraph StatMech StatMech.FrontierA StatMech.FrontierA.MetricCriticalIsoradialClosedFlatSurfaceEmbedding


/--
[character_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean)
-/
@[path]
private lemma character_ne_eq
  [Fintype E]
  [DecidableEq E]
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding g G DualVertex Qprimal Qdual}
  {F : Finset (finiteGraphEdge G)}
  {boundary : Fin (embedding.polygonalAtlas.cellular.ribbonSystem.boundaryComponents F)} :
-- imply
  embedding.character F boundary ≠ 0 := by
-- proof
  apply StatMech.FrontierA.MetricCriticalIsoradialClosedFlatSurfaceEmbedding.character_ne embedding F boundary

/--
[character_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean)
-/
@[path]
private lemma character_total_eq
  [Fintype E]
  [DecidableEq E]
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding g G DualVertex Qprimal Qdual}
  {F : Finset (finiteGraphEdge G)} :
-- imply
  ∏ boundary, embedding.character F boundary = 1 := by
-- proof
  apply StatMech.FrontierA.MetricCriticalIsoradialClosedFlatSurfaceEmbedding.character_total embedding F

/--
[primalExceptional_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean)
-/
@[path]
private lemma primalExceptional_iff_eq
  [Fintype E]
  [DecidableEq E]
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding g G DualVertex Qprimal Qdual}
  {vertex : V} :
-- imply
  embedding.primalExceptional vertex = true ↔ embedding.primalConeIndex vertex % 2 = 1 := by
-- proof
  apply StatMech.FrontierA.MetricCriticalIsoradialClosedFlatSurfaceEmbedding.primalExceptional_iff embedding vertex

/--
[dualExceptional_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean)
-/
@[path]
private lemma dualExceptional_iff_eq
  [Fintype E]
  [DecidableEq E]
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding g G DualVertex Qprimal Qdual}
  {vertex : DualVertex} :
-- imply
  embedding.dualExceptional vertex = true ↔ embedding.dualConeIndex vertex % 2 = 1 := by
-- proof
  apply StatMech.FrontierA.MetricCriticalIsoradialClosedFlatSurfaceEmbedding.dualExceptional_iff embedding vertex

/--
[coneIndexGaussBonnet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean)
-/
@[path]
private lemma coneIndexGaussBonnet_eq
  [Fintype E]
  [DecidableEq E]
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding g G DualVertex Qprimal Qdual} :
-- imply
  (∑ vertex : V, embedding.primalConeIndex vertex) + (∑ vertex : DualVertex, embedding.dualConeIndex vertex) + 1 = g := by
-- proof
  apply StatMech.FrontierA.MetricCriticalIsoradialClosedFlatSurfaceEmbedding.coneIndexGaussBonnet embedding

/--
[surface_kacWard_arf_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean)
-/
@[path]
private lemma surface_kacWard_arf_formula_eq
  [Fintype E]
  [DecidableEq E]
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding g G DualVertex Qprimal Qdual}
-- given
  (weight : Sym2 V -> Real) :
-- imply
  (forall lambda : SurfaceSpinStructure g, (1 - surfaceTwistedKacWardMatrix G embedding.toCriticalIsoradialClosedFlatSurfaceEmbedding.atlas.phase embedding.polygonalAtlas.edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G embedding.polygonalAtlas.edgeClass weight) lambda : Complex)) /\ surfaceUnsignedSectorSum (surfaceGraphSectorWeight G embedding.polygonalAtlas.edgeClass weight) = ((2 : Real) ^ g)⁻¹ * ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot (surfaceGraphSectorWeight G embedding.polygonalAtlas.edgeClass weight) lambda := by
-- proof
  apply StatMech.FrontierA.MetricCriticalIsoradialClosedFlatSurfaceEmbedding.surface_kacWard_arf_formula embedding weight

/--
[normalized_kacWard_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean)
-/
@[path]
private lemma normalized_kacWard_duality_eq
  [Fintype E]
  [DecidableEq E]
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding g G DualVertex Qprimal Qdual} :
-- imply
  kwIsoradialDualityNormalization DualVertex (fun edge => Real.pi / 2 - embedding.theta edge) * (1 - embedding.dualKacWard).det = kwIsoradialDualityNormalization V embedding.theta * (1 - embedding.primalKacWard).det := by
-- proof
  apply StatMech.FrontierA.MetricCriticalIsoradialClosedFlatSurfaceEmbedding.normalized_kacWard_duality embedding


-- created on 2026-10-23
