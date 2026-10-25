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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part105
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

@[simp] theorem boxVertOfCoords3_hasCoords
    (n : ℕ) (x y z : ℤ)
    (hx : x.natAbs ≤ n) (hy : y.natAbs ≤ n) (hz : z.natAbs ≤ n) :
    boxVertHasCoords3 (boxVertOfCoords3 n x y z hx hy hz) x y z := by
  simp [boxVertOfCoords3, boxVertHasCoords3, ising3DSiteOfCoords]


theorem exists_boxVertHasCoords3_of_natAbs_le
    {n : ℕ} {x y z : ℤ}
    (hx : x.natAbs ≤ n) (hy : y.natAbs ≤ n) (hz : z.natAbs ≤ n) :
    ∃ w : FK.boxVerts 3 n, boxVertHasCoords3 w x y z :=
  ⟨boxVertOfCoords3 n x y z hx hy hz, by simp⟩


end Exact3D
end StatMech
