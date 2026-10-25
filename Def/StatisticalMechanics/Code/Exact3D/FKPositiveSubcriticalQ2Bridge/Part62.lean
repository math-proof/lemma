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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part59
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def finiteBoundaryGhostCollapsedCutoffDecrementIndex
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    FinsetFiberIndex
      (Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostCollapsedTwoPointSourceData n v)) where
  α :=
    {a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α //
      a.2.1.1 ∈ finiteBoundaryGhostOnePointSourceCutoff Ω}
  domain :=
    by
      classical
      exact
        Finset.subtype
          (fun a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α =>
            a.2.1.1 ∈ finiteBoundaryGhostOnePointSourceCutoff Ω)
          (finiteBoundaryGhostCutoffDecrementIndex Ω).domain
  map := fun a =>
    ⟨a.1.1.1,
      finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData
        a.1.2.1.1 a.1.1.1
        (by
          exact (Finset.mem_filter.mp a.2).2)
        a.1.2.2.2⟩


noncomputable def finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    FinsetFiberIndex (finiteBoundaryGhostCollapsedTwoPointSourceData n v) where
  α :=
    Sigma (fun m :
      {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
        m ∈ finiteBoundaryGhostOnePointSourceCutoff Ω} =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m.1 v)
  domain :=
    (finiteBoundaryGhostOnePointSourceCutoff Ω).attach.sigma
      (fun m =>
        (Finset.univ :
          Finset
            (finiteBoundaryGhostDecrementedSourceWeightVertexFiber
              n m.1 v)))
  map := fun a =>
    finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData
      a.1.1 v
      (by
        exact (Finset.mem_filter.mp a.1.2).2)
      a.2.2


noncomputable def
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (a : (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).α) :
    (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).α :=
  ⟨⟨⟨v, hv⟩,
      ⟨⟨a.1.1, (Finset.mem_filter.mp a.1.2).1⟩, a.2⟩⟩,
    a.1.2⟩

end Exact3D
end StatMech
