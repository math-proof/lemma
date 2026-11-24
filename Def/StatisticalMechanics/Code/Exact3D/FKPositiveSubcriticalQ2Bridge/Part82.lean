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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part79
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

def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
          ∀ Ω : Finset (Sigma (fun m :
            ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
            finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)),
            (∑ a ∈ Ω,
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
                  β H n v a) ≤
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
          ∀ Ω : Finset (Sigma (fun m :
            ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
            finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)),
            ∃ k : ℕ,
            ∃ label : Sigma (fun m :
              ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
              finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) →
                Fin k,
            ∃ A : Fin k → ℝ,
              (∀ i : Fin k,
                (∑ a ∈ Ω.filter (fun a => label a = i),
                    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
                      β H n v a) ≤ A i) ∧
              (∑ i : Fin k, A i) ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v


end Exact3D
end StatMech
