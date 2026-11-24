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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part63
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

noncomputable section

set_option maxHeartbeats 800000 in


def finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)) :
    {a // a ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d} →
      Sigma (fun m :
        {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
          m ∈ Ω} =>
        {p // p ∈
          finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
            m.1 d.1 d.2}) := by
  classical
  rcases d with ⟨v, d⟩
  rintro ⟨⟨w, m, p⟩, ha⟩
  let c :=
    finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice
      Ω d ha
  have hc : c ∈
      finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
        m.1 v d :=
    finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_mem
      Ω d ha
  exact ⟨m, ⟨c, hc⟩⟩

end
end Exact3D
end StatMech
