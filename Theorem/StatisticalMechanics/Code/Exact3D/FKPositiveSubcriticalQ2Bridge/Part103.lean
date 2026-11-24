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
public import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part105
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
