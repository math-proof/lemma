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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part57
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
