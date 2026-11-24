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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part53
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

set_option linter.style.longLine false in


noncomputable def
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    FinsetFiberIndex
      (finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v) where
  α :=
    Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)
  domain :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
      n Ω v
  map := fun a =>
    ⟨Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)) ∆
        ({some v, none} : Finset (Option (FK.boxVerts 3 n))),
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData
        n v a⟩

end Exact3D
end StatMech
