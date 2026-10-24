import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
open Finset SimpleGraph StatMech StatMech.FrontierA StatMech.FrontierA.CriticalIsoradialClosedFlatSurfaceEmbedding


/--
[surface_kacWard_arf_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardAtlas.lean)
-/
@[path]
private lemma surface_kacWard_arf_formula_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {DualVertex Q Qstar : Type u}
  [Fintype DualVertex]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype Qstar]
  [DecidableEq Qstar]
  {embedding : CriticalIsoradialClosedFlatSurfaceEmbedding g G DualVertex Q Qstar}
-- given
  (weight : Sym2 V -> Real) :
-- imply
  (forall lambda : SurfaceSpinStructure g, (1 - surfaceTwistedKacWardMatrix G embedding.atlas.phase embedding.atlas.edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G embedding.atlas.edgeClass weight) lambda : Complex)) /\ surfaceUnsignedSectorSum (surfaceGraphSectorWeight G embedding.atlas.edgeClass weight) = ((2 : Real) ^ g)⁻¹ * ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot (surfaceGraphSectorWeight G embedding.atlas.edgeClass weight) lambda := by
-- proof
  apply StatMech.FrontierA.CriticalIsoradialClosedFlatSurfaceEmbedding.surface_kacWard_arf_formula embedding weight

/--
[normalized_kacWard_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardAtlas.lean)
-/
@[path]
private lemma normalized_kacWard_duality_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {DualVertex Q Qstar : Type u}
  [Fintype DualVertex]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype Qstar]
  [DecidableEq Qstar]
  {embedding : CriticalIsoradialClosedFlatSurfaceEmbedding g G DualVertex Q Qstar} :
-- imply
  kwIsoradialDualityNormalization DualVertex (fun edge => Real.pi / 2 - embedding.theta edge) * (1 - embedding.dualKacWard).det = kwIsoradialDualityNormalization V embedding.theta * (1 - embedding.primalKacWard).det := by
-- proof
  apply StatMech.FrontierA.CriticalIsoradialClosedFlatSurfaceEmbedding.normalized_kacWard_duality embedding


-- created on 2026-10-23
