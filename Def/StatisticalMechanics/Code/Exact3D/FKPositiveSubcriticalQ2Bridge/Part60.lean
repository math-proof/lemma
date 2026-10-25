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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part57
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def finiteBoundaryGhostCutoffDecrementIndex
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    FinsetFiberIndex
      (Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v)) where
  α :=
    Sigma (fun v :
      {v : FK.boxVerts 3 n // v ∈ Finset.univ.filter (FK.boxBoundary 3 n)} =>
      Sigma (fun m :
        {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
          m ∈ Ω} =>
        {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 v.1}))
  domain :=
    (Finset.univ.filter (FK.boxBoundary 3 n)).attach.sigma
      (fun v =>
        Ω.attach.sigma
          (fun m =>
            (finiteBoundaryGhostBoundaryCrossingPairs m.1 v.1).attach))
  map := fun a =>
    ⟨a.1.1,
      finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := a.2.2.1) a.2.1.1 a.1.1 a.2.2.2⟩


noncomputable def finiteBoundaryGhostSigmaTwoPointSourceDataWeight
    (β H : ℝ) {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)) : ℝ :=
  finiteBoundaryGhostTwoPointSourceDataWeight β H d.2

end Exact3D
end StatMech
