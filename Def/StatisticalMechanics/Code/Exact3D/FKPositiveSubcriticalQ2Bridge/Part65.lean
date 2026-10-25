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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part62
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {w : {w : FK.boxVerts 3 n //
      w ∈ Finset.univ.filter (FK.boxBoundary 3 n)}}
    {m : {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
      m ∈ Ω}}
    {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 w.1}}
    (ha : (⟨w, ⟨m, p⟩⟩ :
      (finiteBoundaryGhostCutoffDecrementIndex Ω).α) ∈
      (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
        (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostTwoPointSourceData n v))) :
    {p' // p' ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 v} :=
  Classical.choose
    (finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_exists_localFiber
      Ω d ha)

end Exact3D
end StatMech
