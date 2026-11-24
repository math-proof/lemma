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
public import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part51
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

theorem finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
    0 ≤
      finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
        β H m v p := by
  classical
  unfold finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
  refine mul_nonneg (mul_nonneg hβ hH) ?_
  refine mul_nonneg ?_ ?_
  · by_cases hsource :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update m p.2.1 (m p.2.1 - 1)))
          (copyDeletePreimageDecrementEraseFinset
            (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
    · simp [hsource]
    · simp [hsource]
  · exact
      weight_ofEdgeFun_nonneg_of_nonneg
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        hβ
        (boundaryGhostCoupling_nonneg
          (FK.boxBoundary 3 n) hH (fun _ => by norm_num))
        (Function.update m p.2.1 (m p.2.1 - 1))


theorem finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (p : finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) :
    0 ≤
      finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand
        β H n m v p :=
  finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_nonneg
    (β := β) (H := H) hβ hH m v p.1


theorem finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_nonneg
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
    0 ≤
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
        β H n v a :=
  finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand_nonneg
    (β := β) (H := H) hβ hH a.1 v a.2


end Exact3D
end StatMech
