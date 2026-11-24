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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part29
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

noncomputable def finiteBoundaryGhostBoundaryCrossingSourceSector
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    Finset (Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :=
  (finiteBoundaryGhostSourceSector m).filter
    (fun K =>
      ∃ i ∈ K,
        some v ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
        none ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i)


noncomputable def finiteBoundaryGhostBoundaryCrossingCopyCount
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m)) : ℕ :=
  (K.filter
    (fun i =>
      some v ∈ Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
      none ∈ Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i)).card


noncomputable def finiteBoundaryGhostBoundaryCrossingPairCount
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) : ℕ :=
  ∑ K ∈ finiteBoundaryGhostSourceSector m,
    finiteBoundaryGhostBoundaryCrossingCopyCount m v K


noncomputable def finiteBoundaryGhostBoundaryCrossingPairs
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    Finset (Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :=
  (finiteBoundaryGhostSourceSector m).sigma
    (fun K => K.filter
      (fun i =>
        some v ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
        none ∈ Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i))


end Exact3D
end StatMech
