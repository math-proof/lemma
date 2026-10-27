import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardLocalGeometry.Part3
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[surfaceIntersection_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean)
-/
@[path]
private lemma surfaceIntersection_add_left_eq
  {g : Nat}
-- given
  (h k l : SurfaceHomology g) :
-- imply
  surfaceIntersection (h + k) l = surfaceIntersection h l + surfaceIntersection k l := by
-- proof
  apply StatMech.FrontierA.surfaceIntersection_add_left h k l

/--
[surfaceIntersection_finset_sum_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean)
-/
@[path]
private lemma surfaceIntersection_finset_sum_left_eq
  {g : Nat}
  [DecidableEq I]
  {S : Finset I}
-- given
  (f : I -> SurfaceHomology g)
  (h : SurfaceHomology g) :
-- imply
  surfaceIntersection (∑ i ∈ S, f i) h = ∑ i ∈ S, surfaceIntersection (f i) h := by
-- proof
  apply StatMech.FrontierA.surfaceIntersection_finset_sum_left S f h

/--
[surfaceIntersection_subgraphHomology_eq_doubleSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean)
-/
@[path]
private lemma surfaceIntersection_subgraphHomology_eq_doubleSum_eq
  {g : Nat}
  [DecidableEq V]
  {F K : Finset (Sym2 V)}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g) :
-- imply
  surfaceIntersection (surfaceSubgraphHomology edgeClass F) (surfaceSubgraphHomology edgeClass K) = ∑ edge ∈ F, ∑ other ∈ K, surfaceIntersection (edgeClass edge) (edgeClass other) := by
-- proof
  apply StatMech.FrontierA.surfaceIntersection_subgraphHomology_eq_doubleSum edgeClass F K

/--
[SurfaceLocalSpinorGeometry.path_phase_sq_mul_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean)
-/
@[path]
private lemma path_phase_sq_mul_direction_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {geometry : SurfaceLocalSpinorGeometry g G}
  {N : Nat}
-- given
  (path : Fin (N + 1) -> G.Dart)
  (hvalid : forall j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) /\ (path j.castSucc).edge ≠ (path j.succ).edge) :
-- imply
  (∏ j : Fin N, geometry.phase (path j.castSucc) (path j.succ)) ^ 2 * geometry.direction (path 0) = geometry.direction (path (Fin.last N)) := by
-- proof
  apply StatMech.FrontierA.SurfaceLocalSpinorGeometry.path_phase_sq_mul_direction geometry path hvalid

/--
[SurfaceLocalSpinorGeometry.path_phase_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean)
-/
@[path]
private lemma path_phase_sq_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {geometry : SurfaceLocalSpinorGeometry g G} :
-- imply
  forall {N : Nat} (path : Fin (N + 1) -> G.Dart), path (Fin.last N) = (path 0).symm -> (forall j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) /\ (path j.castSucc).edge ≠ (path j.succ).edge) -> (∏ j : Fin N, geometry.phase (path j.castSucc) (path j.succ)) ^ 2 = -1 := by
-- proof
  apply StatMech.FrontierA.SurfaceLocalSpinorGeometry.path_phase_sq geometry

/--
[SurfaceLocalSpinorGeometry.closed_phase_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean)
-/
@[path]
private lemma closed_phase_sq_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {geometry : SurfaceLocalSpinorGeometry g G} :
-- imply
  forall {n : Nat} [NeZero n] (loop : Fin n -> G.Dart), (forall k : Fin n, G.DartAdj (loop k) (loop (k + 1)) /\ (loop k).edge ≠ (loop (k + 1)).edge) -> (∏ k, geometry.phase (loop k) (loop (k + 1))) ^ 2 = 1 := by
-- proof
  apply StatMech.FrontierA.SurfaceLocalSpinorGeometry.closed_phase_sq geometry

/--
[SurfaceLocalSpinorGeometry.intersection_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean)
-/
@[path]
private lemma intersection_formula_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {geometry : SurfaceLocalSpinorGeometry g G}
  {F K : Finset (Sym2 V)} :
-- imply
  surfaceIntersection (surfaceSubgraphHomology geometry.edgeClass F) (surfaceSubgraphHomology geometry.edgeClass K) = ∑ edge ∈ F, ∑ other ∈ K, surfaceIntersection (geometry.edgeClass edge) (geometry.edgeClass other) := by
-- proof
  apply StatMech.FrontierA.SurfaceLocalSpinorGeometry.intersection_formula geometry F K

/--
[admissible_closedFlatSurface_kacWard_arf_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean)
-/
@[path]
private lemma admissible_closedFlatSurface_kacWard_arf_formula_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : AdmissibleClosedFlatSurfaceEmbedding g G}
-- given
  (weight : Sym2 V -> Real) :
-- imply
  (forall lambda : SurfaceSpinStructure g, (1 - surfaceTwistedKacWardMatrix G embedding.geometry.phase embedding.geometry.edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G embedding.geometry.edgeClass weight) lambda : Complex)) /\ surfaceUnsignedSectorSum (surfaceGraphSectorWeight G embedding.geometry.edgeClass weight) = ((2 : Real) ^ g)⁻¹ * ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot (surfaceGraphSectorWeight G embedding.geometry.edgeClass weight) lambda := by
-- proof
  apply StatMech.FrontierA.admissible_closedFlatSurface_kacWard_arf_formula G embedding weight


-- created on 2026-10-23
