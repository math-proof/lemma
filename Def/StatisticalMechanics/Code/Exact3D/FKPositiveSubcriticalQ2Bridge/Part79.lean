module
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
public import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part76
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

noncomputable def finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  ∑ v ∈ Finset.univ.filter
      (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
    (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
      ((β * H) *
        edgeCopySourcePairEmptyCollapsedSum
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))


noncomputable def
    finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  ∑ v ∈ Finset.univ.filter
      (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
    (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
      (((β * H) / Real.tanh (β * H)) *
        edgeCopySourcePairEmptyCollapsedSum
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))


end Exact3D
end StatMech
