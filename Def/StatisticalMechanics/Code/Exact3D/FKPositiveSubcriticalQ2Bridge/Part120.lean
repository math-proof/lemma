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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part117
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (C : ℝ) (k : ℕ) (tension : SurfaceVec3 → ℝ)
      (boundaryCoord : (n : ℕ) → FK.boxVerts 3 n → SurfaceVec3),
      0 < C ∧
      ConvexOn ℝ Set.univ tension ∧
      (∀ x y z : ℝ,
        tension (surfaceVec3 x (-y) (-z)) = tension (surfaceVec3 x y z)) ∧
      (∀ t : ℝ, 0 ≤ t →
        tension (surfaceVec3 t 0 0) = t * tension surfaceXAxisUnit) ∧
      (∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
          ∃ a b : ℝ, boundaryCoord n v = surfaceVec3 (n : ℝ) a b) ∧
      (∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
          ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
            ≤ C * (n : ℝ) ^ k *
              Real.exp (-(tension (boundaryCoord n v)))) ∧
      Tendsto
        (fun n : ℕ =>
          -Real.log (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n) /
            (n : ℝ)) atTop (nhds (tension surfaceXAxisUnit))


def
    FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (C : ℝ) (k : ℕ) (tension : SurfaceVec3 → ℝ), 0 < C ∧
      ConvexOn ℝ Set.univ tension ∧
      (∀ x y z : ℝ,
        tension (surfaceVec3 (-x) y z) = tension (surfaceVec3 x y z)) ∧
      (∀ x y z : ℝ,
        tension (surfaceVec3 x (-y) z) = tension (surfaceVec3 x y z)) ∧
      (∀ x y z : ℝ,
        tension (surfaceVec3 x y (-z)) = tension (surfaceVec3 x y z)) ∧
      (∀ x y z : ℝ,
        tension (surfaceVec3 y x z) = tension (surfaceVec3 x y z)) ∧
      (∀ x y z : ℝ,
        tension (surfaceVec3 z y x) = tension (surfaceVec3 x y z)) ∧
      (∀ t : ℝ, 0 ≤ t →
        tension (surfaceVec3 t 0 0) = t * tension surfaceXAxisUnit) ∧
      (∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
          ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
            ≤ C * (n : ℝ) ^ k *
              Real.exp (-(tension (surfaceVecOfBoxVertex n v)))) ∧
      Tendsto
        (fun n : ℕ =>
          -Real.log (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n) /
            (n : ℝ)) atTop (nhds (tension surfaceXAxisUnit))


end Exact3D
end StatMech
