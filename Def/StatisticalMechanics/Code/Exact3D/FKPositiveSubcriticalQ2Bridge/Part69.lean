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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part66
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

noncomputable def
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementDecrementData
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1)
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
    finiteBoundaryGhostTwoPointSourceData n d.1 :=
  ⟨Function.update d.2.toSourceData.1 i.1
      (d.2.toSourceData.1 i.1 - 1),
    ⟨copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
        d.2.toSourceData.2.1,
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_mem_twoPointSourceSector
        d hi⟩⟩


end Exact3D
end StatMech
