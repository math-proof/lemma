import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFiniteWeightedBoundaryError_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma isingFiniteWeightedBoundaryError_nonneg_eq
  [Fintype V]
  [Nonempty V]
  {data target : V → Real}
-- given
  (boundary : V → Prop) :
-- imply
  0 ≤ isingFiniteWeightedBoundaryError boundary data target := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedBoundaryError_nonneg boundary data target

/--
[isingFiniteWeightedBoundaryError_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma isingFiniteWeightedBoundaryError_bound_eq
  [Fintype V]
  [Nonempty V]
  {data target : V → Real}
  {x : V}
-- given
  (boundary : V → Prop)
  (hx : boundary x) :
-- imply
  |data x - target x| ≤ isingFiniteWeightedBoundaryError boundary data target := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedBoundaryError_bound boundary data target x hx

/--
[isingFiniteWeightedTargetResidual_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma isingFiniteWeightedTargetResidual_nonneg_eq
  [Fintype V]
  [Nonempty V]
  {conductance : V → V → Real}
  {target : V → Real}
-- given
  (boundary : V → Prop) :
-- imply
  0 ≤ isingFiniteWeightedTargetResidual conductance boundary target := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedTargetResidual_nonneg conductance boundary target

/--
[isingFiniteWeightedTargetResidual_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma isingFiniteWeightedTargetResidual_bound_eq
  [Fintype V]
  [Nonempty V]
  {conductance : V → V → Real}
  {target : V → Real}
  {x : V}
-- given
  (boundary : V → Prop)
  (hx : ¬ boundary x) :
-- imply
  |isingFiniteWeightedLaplacian conductance target x| ≤ isingFiniteWeightedTargetResidual conductance boundary target := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedTargetResidual_bound conductance boundary target x hx

/--
[vertexBoundaryConsistencyError_fixed_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma vertexBoundaryConsistencyError_fixed_bound_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullVertexNode n) → Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hx : fkIsingSquareFullVertexFixedBoundary n x) :
-- imply
  |0 - target (some x)| ≤ vertexBoundaryConsistencyError n hn target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryConsistencyError_fixed_bound n hn target x hx

/--
[vertexBoundaryConsistencyError_ghost_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma vertexBoundaryConsistencyError_ghost_bound_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullVertexNode n) → Real}
-- given
  (hn : 0 < n) :
-- imply
  |1 - target none| ≤ vertexBoundaryConsistencyError n hn target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBoundaryConsistencyError_ghost_bound n hn target

/--
[faceBoundaryConsistencyError_fixed_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma faceBoundaryConsistencyError_fixed_bound_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullFaceNode n) → Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hc : fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  |1 - target (some c)| ≤ faceBoundaryConsistencyError n hn target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryConsistencyError_fixed_bound n hn target c hc

/--
[faceBoundaryConsistencyError_ghost_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma faceBoundaryConsistencyError_ghost_bound_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullFaceNode n) → Real}
-- given
  (hn : 0 < n) :
-- imply
  |0 - target none| ≤ faceBoundaryConsistencyError n hn target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceBoundaryConsistencyError_ghost_bound n hn target

/--
[vertexTargetResidual_robin_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma vertexTargetResidual_robin_bound_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullVertexNode n) → Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hx : ¬ fkIsingSquareFullVertexFixedBoundary n x) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y ↦ target (some y)) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (target none - target (some x))| ≤ vertexTargetResidual n target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexTargetResidual_robin_bound n target x hx

/--
[faceTargetResidual_robin_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma faceTargetResidual_robin_bound_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullFaceNode n) → Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d ↦ target (some d)) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (target none - target (some c))| ≤ faceTargetResidual n target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceTargetResidual_robin_bound n target c hc

/--
[vertexDirichlet_target_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma vertexDirichlet_target_error_le_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullVertexNode n) → Real}
-- given
  (hn : 0 < n) :
-- imply
  ∀ x, |vertexDirichlet n hn x - target x| ≤ vertexTargetConsistencyError n hn target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexDirichlet_target_error_le n hn target

/--
[faceDirichlet_target_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma faceDirichlet_target_error_le_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullFaceNode n) → Real}
-- given
  (hn : 0 < n) :
-- imply
  ∀ c, |faceDirichlet n hn c - target c| ≤ faceTargetConsistencyError n hn target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceDirichlet_target_error_le n hn target

/--
[physicalIncidence_target_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma physicalIncidence_target_error_le_eq
  {n : Nat}
  {vertexTarget : Option (FKIsingSquareFullVertexNode n) → Real}
  {faceTarget : Option (FKIsingSquareFullFaceNode n) → Real}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
  {target : Real}
-- given
  (hn : 0 < n)
  (hvertexTarget : vertexTarget (some (fkIsingSquareInteriorRadialEndpoint n hn e)) = target)
  (hfaceTarget : faceTarget (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) = target) :
-- imply
  |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) - target| ≤ max (vertexTargetConsistencyError n hn vertexTarget) (faceTargetConsistencyError n hn faceTarget) ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) - target| ≤ max (vertexTargetConsistencyError n hn vertexTarget) (faceTargetConsistencyError n hn faceTarget) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_target_error_le n hn vertexTarget faceTarget e target hvertexTarget hfaceTarget

/--
[physicalIncidence_uniform_convergence_of_weightedConsistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean)
-/
@[path]
private lemma physicalIncidence_uniform_convergence_of_weightedConsistency_eq
  {N : Nat → Nat}
-- given
  (hN : ∀ k, 0 < N k)
  (vertexTarget : ∀ k, Option (FKIsingSquareFullVertexNode (N k)) → Real)
  (faceTarget : ∀ k, Option (FKIsingSquareFullFaceNode (N k)) → Real)
  (incidenceTarget : ∀ k, FKIsingSquareInteriorRadialIncidence (N k) (hN k) → Real)
  (hvertexTarget : ∀ k e, vertexTarget k (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) = incidenceTarget k e)
  (hfaceTarget : ∀ k e, faceTarget k (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) = incidenceTarget k e)
  (hconsistency : Tendsto (fun k ↦ max (vertexTargetConsistencyError (N k) (hN k) (vertexTarget k)) (faceTargetConsistencyError (N k) (hN k) (faceTarget k))) atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop, ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - incidenceTarget k e| < eta ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - incidenceTarget k e| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_uniform_convergence_of_weightedConsistency N hN vertexTarget faceTarget incidenceTarget hvertexTarget hfaceTarget hconsistency


-- created on 2026-10-23
