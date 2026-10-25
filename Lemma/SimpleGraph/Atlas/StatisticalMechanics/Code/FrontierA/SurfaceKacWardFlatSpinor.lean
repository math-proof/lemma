import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[surfaceParitySign_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma surfaceParitySign_ne_zero_eq
  {z : Fin 2} :
-- imply
  surfaceParitySign z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.surfaceParitySign_ne_zero z

/--
[kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant'_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)}
  {n : Nat}
  [NeZero n]
-- given
  (phase : G.Dart -> G.Dart -> Complex)
  (hrev : KWGraphLoopReversalInvariant G phase)
  (hdeg : forall vertex, G.degree vertex <= 3)
  (loop : Fin n -> G.Dart)
  (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
-- imply
  kwGraphFormalLogCoeff G phase (ons_finsetExponent S) = -kwGraphLoopScalar G phase loop := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant' G phase hrev hdeg S loop hloop

/--
[edge_toFinset_subset_walk_verts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma edge_toFinset_subset_walk_verts_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
  {edge : Sym2 V}
-- given
  (hedge : edge ∈ p.edges.toFinset) :
-- imply
  (edge.toFinset : Set V) ⊆ p.toSubgraph.verts := by
-- proof
  apply StatMech.FrontierA.edge_toFinset_subset_walk_verts p hedge

/--
[SurfaceFlatSpinorEmbedding.disjointCycleIsotropic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma disjointCycleIsotropic_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : SurfaceFlatSpinorEmbedding g G} :
-- imply
  SurfaceDisjointCycleIsotropic G embedding.edgeClass := by
-- proof
  apply StatMech.FrontierA.SurfaceFlatSpinorEmbedding.disjointCycleIsotropic embedding

/--
[SurfaceFlatSpinorEmbedding.loopReversalInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma loopReversalInvariant_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : SurfaceFlatSpinorEmbedding g G} :
-- imply
  KWGraphLoopReversalInvariant G embedding.phase := by
-- proof
  apply StatMech.FrontierA.SurfaceFlatSpinorEmbedding.loopReversalInvariant embedding

/--
[SurfaceFlatSpinorEmbedding.simpleCycleLogCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma simpleCycleLogCoeff_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : SurfaceFlatSpinorEmbedding g G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  kwGraphFormalLogCoeff G embedding.phase (ons_finsetExponent p.edges.toFinset) = surfaceBaseCycleCoefficient embedding.edgeClass p.edges.toFinset := by
-- proof
  apply StatMech.FrontierA.SurfaceFlatSpinorEmbedding.simpleCycleLogCoeff embedding p hp

/--
[SurfaceFlatSpinorEmbedding.weightedCycleLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma weightedCycleLog_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : SurfaceFlatSpinorEmbedding g G} :
-- imply
  KWGraphWeightedCycleLog G embedding.phase (surfaceBaseCycleCoefficient embedding.edgeClass) := by
-- proof
  apply StatMech.FrontierA.SurfaceFlatSpinorEmbedding.weightedCycleLog embedding

/--
[SurfaceFlatSpinorEmbedding.formalRoot_nonsquarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma formalRoot_nonsquarefree_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : SurfaceFlatSpinorEmbedding g G}
  {m : Sym2 V →₀ Nat}
-- given
  (hm : ¬ ons_IsSquarefreeExponent m) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G embedding.phase) = 0 := by
-- proof
  apply StatMech.FrontierA.SurfaceFlatSpinorEmbedding.formalRoot_nonsquarefree embedding m hm

/--
[surface_flatSpinor_kacWard_det_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma surface_flatSpinor_kacWard_det_square_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : SurfaceFlatSpinorEmbedding g G}
  {lambda : SurfaceSpinStructure g}
-- given
  (weight : Sym2 V -> Complex) :
-- imply
  (1 - surfaceTwistedKacWardMatrix G embedding.phase embedding.edgeClass lambda weight).det = surfaceQuadraticEvenPolynomial G embedding.edgeClass lambda weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.surface_flatSpinor_kacWard_det_square G embedding lambda weight

/--
[surface_flatSpinor_kacWard_arf_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean)
-/
@[path]
private lemma surface_flatSpinor_kacWard_arf_formula_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : SurfaceFlatSpinorEmbedding g G}
-- given
  (weight : Sym2 V -> Real) :
-- imply
  (forall lambda : SurfaceSpinStructure g, (1 - surfaceTwistedKacWardMatrix G embedding.phase embedding.edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G embedding.edgeClass weight) lambda : Complex)) /\ surfaceUnsignedSectorSum (surfaceGraphSectorWeight G embedding.edgeClass weight) = ((2 : Real) ^ g)⁻¹ * ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot (surfaceGraphSectorWeight G embedding.edgeClass weight) lambda := by
-- proof
  apply StatMech.FrontierA.surface_flatSpinor_kacWard_arf_formula G embedding weight


-- created on 2026-10-23
