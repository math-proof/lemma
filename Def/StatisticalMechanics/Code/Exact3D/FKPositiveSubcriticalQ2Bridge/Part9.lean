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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part8
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
    FreeQ2BoundaryProfileBoundaryVertexEnvelopeForFixedInnerSameMassPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ (Alo AfkHi : ℕ → ℝ) (mass : ℝ),
      0 < mass →
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo AfkHi mass →
      ∃ (Apoint Acount : ℕ → ℝ),
        PositiveSubexponentialPrefactor Apoint ∧
          PositiveSubexponentialPrefactor Acount ∧
          (∀ᶠ n in atTop,
            ((Finset.univ.filter
              (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ)
              ≤ Acount n) ∧
          ∀ᶠ n in atTop,
            ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
              ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
                  (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                  (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
                ≤ Apoint n * Real.exp (-(mass * (n : ℝ)))


end Exact3D
end StatMech
