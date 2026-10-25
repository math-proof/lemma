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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part40
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostBoundaryCrossingPairDecrementImage_mem
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v) :
    d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v ↔
      ∃ p, ∃ hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
        finiteBoundaryGhostBoundaryCrossingPairDecrementData m v hp = d := by
  classical
  letI : DecidableEq (finiteBoundaryGhostTwoPointSourceData n v) :=
    Classical.decEq _
  rw [finiteBoundaryGhostBoundaryCrossingPairDecrementImage, Finset.mem_image]
  constructor
  · rintro ⟨p, _hp, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementImage_card_le
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v).card ≤
      (finiteBoundaryGhostBoundaryCrossingPairs m v).card := by
  classical
  letI : DecidableEq (finiteBoundaryGhostTwoPointSourceData n v) :=
    Classical.decEq _
  have hcard :
      ((finiteBoundaryGhostBoundaryCrossingPairs m v).attach.image
        (fun p =>
          finiteBoundaryGhostBoundaryCrossingPairDecrementData
            (p := p.1) m v p.2)).card ≤
        (finiteBoundaryGhostBoundaryCrossingPairs m v).attach.card :=
    Finset.card_image_le
  simpa [finiteBoundaryGhostBoundaryCrossingPairDecrementImage,
    Finset.card_attach] using hcard


end Exact3D
end StatMech
