/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part67
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_sourcePairData
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1)
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
    edgeCopySourcePairData
      (Sharpness.withGhost (FK.boxGraph 3 n))
      (finiteBoundaryGhostOnePointSource 3 n)
      (∅ : Finset (Option (FK.boxVerts 3 n))) :=
  ⟨Function.update d.2.toSourceData.1 i.1
      (d.2.toSourceData.1 i.1 - 1),
    ⟨copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
        d.2.toSourceData.2.1,
      ⟨finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_source
          d hi,
        finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_complement_source
          d hi⟩⟩⟩


noncomputable def
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_sourcePairData
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1)
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
    edgeCopySourcePairData
      (Sharpness.withGhost (FK.boxGraph 3 n))
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
      (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) :=
  ⟨Function.update d.2.toSourceData.1 i.1
      (d.2.toSourceData.1 i.1 - 1),
    ⟨copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
        d.2.toSourceData.2.1,
      ⟨finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_source
          d hi,
        finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_complement_source
          d hi⟩⟩⟩


end Exact3D
end StatMech
