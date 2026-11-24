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
public import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part85
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

theorem finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_nonneg
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω := by
  classical
  unfold finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap
  exact Finset.sum_nonneg
    (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))


theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairs_sum
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ m ∈ Ω,
          ((finiteBoundaryGhostBoundaryCrossingPairs m w).card : ℝ) := by
  exact
    (finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_domain_card
      Ω v).trans
      (finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_card_le_crossingPairs_sum
        Ω)


theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairCap
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω := by
  simpa [finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap] using
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairs_sum
      Ω v


end Exact3D
end StatMech
